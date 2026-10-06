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
shell = kurt.Shell(kurt.RunConfig(comment_indent=comment_indent, kurtc=True))
result = shell.start_file('/play/proof.kurt')
output = kurt.hello() + '\\n' + result.output.rstrip('\\n') + ('\\n' + result.error if result.error else '')
json.dumps({'output': output, 'ok': result.ok, 'shell': json.loads(shell_state())})
`);
  const data = JSON.parse(result);
  let certificate = null;
  if (data.ok) { try { certificate = pyodide.FS.readFile('/play/proof.kurtc', { encoding: 'utf8' }); } catch {} }
  postMessage({ type: 'result', output: data.output, exitCode: data.ok ? 0 : 1, certificate, shell: data.shell });
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

self.onmessage = async ({ data }) => {
  if (!pyodide) return;
  try {
    if (data.type === 'run') await runProof(data);
    else if (data.type === 'shell') shellLine(data);
    else if (data.type === 'complete') complete(data);
  } catch (error) { postMessage({ type: 'error', message: error?.message || String(error) }); }
};
initialize().catch(error => postMessage({ type: 'error', message: error?.message || String(error) }));
