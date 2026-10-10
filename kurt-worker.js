const PYODIDE_URL = 'https://cdn.jsdelivr.net/pyodide/v0.26.2/full/';
let pyodide;

async function initialize() {
  importScripts(`${PYODIDE_URL}pyodide.js`);
  pyodide = await loadPyodide({ indexURL: PYODIDE_URL });
  const response = await fetch('kurt.py', { cache: 'no-store' });
  if (!response.ok) throw new Error(`Could not load Kurt (${response.status})`);
  const source = await response.text();
  pyodide.FS.writeFile('/kurt.py', source, { encoding: 'utf8' });
  try { pyodide.FS.mkdir('/play'); } catch {}
  pyodide.FS.chdir('/play');
  // Kurt as a module: a run is a `kurt.Shell`, which then continues where the check stopped
  pyodide.runPython(`
import sys, json
sys.path.insert(0, '/')
import kurt
shell = None
def shell_state():
    return json.dumps({'stopped': shell.stopped, 'line': shell.line, 'indent': shell.indentation(),
                       'next': shell.next_steps(), 'summary': shell.summary(), 'accepted': shell.accepted})
`);
  // the editor (index.html; editor.js): Kurt's language server, as the editors use it -- the reasons of the
  // lines (inlay hints), the errors and todos (diagnostics), and what a line is (hover)
  pyodide.runPython(`
class _Captured:
    # what the server sends (its JSON-RPC messages), instead of writing them to stdout
    def __init__(self): self.messages = []
    def write(self, data): self.messages.append(json.loads(data.split(b'\\r\\n\\r\\n', 1)[1]))
    def flush(self): pass
lsp_out = _Captured()
lsp = kurt.LanguageServer(None, lsp_out)
lsp.handle({'method': 'initialize', 'id': 0, 'params': {'initializationOptions': {'allErrors': True}}})
LSP_URI = 'file:///play/proof.kurt'
def lsp_check(text, version):
    lsp.texts[LSP_URI], lsp.versions[LSP_URI] = text, version
    lsp_out.messages.clear()
    lsp.check(LSP_URI)
    diagnostics = [d for m in lsp_out.messages if m.get('method') == 'textDocument/publishDiagnostics' for d in m['params']['diagnostics']]
    document = {'uri': LSP_URI}
    end = {'line': text.count('\\n') + 1, 'character': 0}
    hints = lsp.inlay_hints({'textDocument': document, 'range': {'start': {'line': 0, 'character': 0}, 'end': end}})
    hovers = {}
    for n in lsp.line_events(LSP_URI):
        hover = lsp.hover({'textDocument': document, 'position': {'line': n, 'character': 0}})
        if hover: hovers[n] = hover['contents']['value']
    result = lsp.results.get(LSP_URI)
    return json.dumps({'version': version, 'diagnostics': diagnostics, 'hints': hints, 'hovers': hovers,
                       'ok': bool(result and result.ok), 'todos': len(result.todos) if result else 0}, ensure_ascii=False)
`);
  const version = source.match(/version\s*=\s*['"]([^'"]+)/)?.[1] || 'unknown';
  postMessage({ type: 'ready', version });
}

async function runProof({ code, indent, files }) {
  pyodide.FS.writeFile('/play/proof.kurt', code, { encoding: 'utf8' });
  // the files the proof loads besides the theories (e.g. a lesson's helper), next to it
  for (const [name, text] of Object.entries(files || {})) {
    if (!name.includes('/')) pyodide.FS.writeFile(`/play/${name}`, text, { encoding: 'utf8' });
  }
  try { pyodide.FS.unlink('/play/proof.kurtc'); } catch {}
  // one run: the output, and the certificate (a complete proof writes `proof.kurtc`)
  pyodide.globals.set('comment_indent', Number(indent));
  const result = pyodide.runPython(`
# the first error only, as \`kurt\` on the command line: the shell continues at the failing line
# (the editor, index.html, shows all errors)
shell = kurt.Shell(kurt.RunConfig(comment_indent=comment_indent, kurtc=True))
result = shell.start_file('/play/proof.kurt')
output = kurt.hello() + '\\n' + result.output.rstrip('\\n') + ('\\n' + result.error if result.error and result.error not in result.output else '')
json.dumps({'output': output, 'ok': result.ok, 'shell': json.loads(shell_state())})
`);
  const data = JSON.parse(result);
  let certificate = null;
  if (data.ok) { try { certificate = pyodide.FS.readFile('/play/proof.kurtc', { encoding: 'utf8' }); } catch {} }
  postMessage({ type: 'result', output: data.output, exitCode: data.ok ? 0 : 1, certificate, shell: data.shell });
}

function checkDocument({ code, version, files }) {
  // the new editor: a check of the whole text, its results by line
  for (const [name, text] of Object.entries(files || {})) {
    if (!name.includes('/')) pyodide.FS.writeFile(`/play/${name}`, text, { encoding: 'utf8' });
  }
  pyodide.globals.set('check_text', code); pyodide.globals.set('check_version', version);
  postMessage({ type: 'checked', ...JSON.parse(pyodide.runPython('lsp_check(check_text, check_version)')) });
}

function shellLine({ text }) {
  // a line (or several) in the shell, where the run stopped
  pyodide.globals.set('shell_text', text);
  const result = pyodide.runPython(`
json.dumps({'output': shell.feed(shell_text), 'shell': json.loads(shell_state())}) if shell else json.dumps({'output': '', 'shell': None})
`);
  postMessage({ type: 'shell-output', ...JSON.parse(result) });
}

function complete({ line, word }) {
  pyodide.globals.set('complete_line', line); pyodide.globals.set('complete_word', word);
  const result = pyodide.runPython(`json.dumps(shell.completions(complete_line, complete_word) if shell else [])`);
  postMessage({ type: 'completions', items: JSON.parse(result), line, word });
}

function editorComplete({ prefix, line, word, files, requestId }) {
  // Reconstruct the proof state immediately before the caret. This is deliberately a separate
  // Session from the output shell: asking for a hint must not change a checked run.
  for (const [name, text] of Object.entries(files || {})) {
    if (!name.includes('/')) pyodide.FS.writeFile(`/play/${name}`, text, { encoding: 'utf8' });
  }
  pyodide.globals.set('editor_prefix', prefix);
  pyodide.globals.set('editor_line', line);
  pyodide.globals.set('editor_word', word);
  const result = pyodide.runPython(`
editor_shell = kurt.Shell()
editor_shell.start_text(editor_prefix, '/play/proof.kurt')
json.dumps(editor_shell.completions(editor_line, editor_word))
`);
  postMessage({ type: 'editor-completions', items: JSON.parse(result), requestId });
}

self.onmessage = async ({ data }) => {
  if (!pyodide) return;
  try {
    if (data.type === 'run') await runProof(data);
    else if (data.type === 'check') checkDocument(data);
    else if (data.type === 'shell') shellLine(data);
    else if (data.type === 'complete') complete(data);
    else if (data.type === 'editor-complete') editorComplete(data);
  } catch (error) { postMessage({ type: 'error', message: error?.message || String(error) }); }
};
initialize().catch(error => postMessage({ type: 'error', message: error?.message || String(error) }));
