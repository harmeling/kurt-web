const PYODIDE_URL = 'https://cdn.jsdelivr.net/pyodide/v0.26.2/full/';
let pyodide;
// the Cancel button (editor.js): a flag in a SharedArrayBuffer, which the page sets while this worker is busy
// with a check (it can't read a message meanwhile). Kurt asks it at every step of the search and every
// line (`LanguageServer.cancel`, `RunConfig.cancel`) and stops there, so the worker -- Pyodide and the
// theories it has checked -- stays. Without a SharedArrayBuffer (a page that isn't cross-origin
// isolated) there is no flag, and the page kills the worker instead.
let cancelFlag = null;
self.kurtCancelled = () => cancelFlag !== null && Atomics.load(cancelFlag, 0) !== 0;

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
# while a check runs: which line of which file (Kurt 0.8.2, \`RunConfig.progress\`), for the progress bar --
# at most 10 times a second, none for a check that takes less than 0.1 s
import time, os.path
from js import postMessage as _post_message, Object as _Object
from pyodide.ffi import to_js as _to_js
_progress_last = [0.0]
def _progress(event):
    now = time.monotonic()
    if now - _progress_last[0] >= 0.1:
        _progress_last[0] = now
        _post_message(_to_js({'type': 'progress', 'version': lsp.versions.get(LSP_URI), **event,
                              'file': os.path.basename(event['file'])}, dict_converter=_Object.fromEntries))
lsp.progress = _progress
# the Cancel button: the flag (kurtCancelled, above), asked by Kurt at every step and line
from js import kurtCancelled as _kurt_cancelled
def _cancelled():
    return bool(_kurt_cancelled())
if hasattr(lsp, 'cancel'):
    lsp.cancel = _cancelled
else:           # (Kurt 0.10.0 and before: the same, through the sessions of the server)
    _session_for = lsp.session_for
    lsp.session_for = lambda uri, cancel=None: _session_for(uri, cancel=lambda: _cancelled() or (cancel is not None and cancel()))
def lsp_check(text, version):
    _progress_last[0] = time.monotonic()
    lsp.texts[LSP_URI], lsp.versions[LSP_URI] = text, version
    lsp_out.messages.clear()
    lsp.check(LSP_URI)
    if _cancelled():        # (the check stopped, nothing was published)
        return json.dumps({'version': version, 'cancelled': True})
    diagnostics = [d for m in lsp_out.messages if m.get('method') == 'textDocument/publishDiagnostics' for d in m['params']['diagnostics']]
    document = {'uri': LSP_URI}
    end = {'line': text.count('\\n') + 1, 'character': 0}
    hints = lsp.inlay_hints({'textDocument': document, 'range': {'start': {'line': 0, 'character': 0}, 'end': end}})
    hovers = {}       # of every line that says something (a declaration, \`parse\`, ... too, as in VS Code)
    for n, line in enumerate(text.split('\\n')):
        if not line.strip(): continue
        hover = lsp.hover({'textDocument': document, 'position': {'line': n, 'character': 0}})
        if hover: hovers[n] = hover['contents']['value']
    result = lsp.results.get(LSP_URI)
    return json.dumps({'version': version, 'diagnostics': diagnostics, 'hints': hints, 'hovers': hovers,
                       'ok': bool(result and result.ok), 'todos': len(result.todos) if result else 0}, ensure_ascii=False)
`);
  const version = source.match(/version\s*=\s*['"]([^'"]+)/)?.[1] || 'unknown';
  postMessage({ type: 'ready', version });
}

// a file the proof loads, next to it in /play -- also in a folder below it (an exercise loads
// its scene with `load theory/island`), but nowhere else
function isPlayFileName(name) {
  const parts = name.split('/');
  return parts.every(part => part && part !== '.' && part !== '..');
}
function writePlayFile(name, text) {
  if (!isPlayFileName(name)) return;
  const parts = name.split('/');
  let dir = '/play';
  for (const part of parts.slice(0, -1)) { dir += `/${part}`; try { pyodide.FS.mkdir(dir); } catch {} }
  pyodide.FS.writeFile(`/play/${name}`, text, { encoding: 'utf8' });
}

async function runProof({ code, indent, files }) {
  pyodide.FS.writeFile('/play/proof.kurt', code, { encoding: 'utf8' });
  // the files the proof loads besides the theories (e.g. a lesson's helper), next to it
  for (const [name, text] of Object.entries(files || {})) {
    writePlayFile(name, text);
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
    writePlayFile(name, text);
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
    writePlayFile(name, text);
  }
  pyodide.globals.set('editor_prefix', prefix);
  pyodide.globals.set('editor_line', line);
  pyodide.globals.set('editor_word', word);
  const result = pyodide.runPython(`
# (the Cancel button stops it too: the worker is busy with it, maybe with a long search, before a check)
editor_shell = kurt.Shell(kurt.RunConfig(cancel=_cancelled))
editor_shell.start_text(editor_prefix, '/play/proof.kurt')
json.dumps([] if _cancelled() else editor_shell.completions(editor_line, editor_word))
`);
  postMessage({ type: 'editor-completions', items: JSON.parse(result), requestId });
}

self.onmessage = async ({ data }) => {
  if (data.type === 'cancel-flag') { cancelFlag = data.flag; return; }      // (sent before Pyodide is loaded)
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
