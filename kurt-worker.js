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
  const result = await pyodide.runPythonAsync(`
import sys, runpy, io, contextlib
sys.argv = ['kurt.py', '--no-kurtc', '-r', '${Number(indent)}', '/play/proof.kurt']
buf_out, buf_err = io.StringIO(), io.StringIO()
exit_code = 0
with contextlib.redirect_stdout(buf_out), contextlib.redirect_stderr(buf_err):
    try:
        runpy.run_path('/kurt.py', run_name='__main__')
    except SystemExit as exc:
        exit_code = exc.code if isinstance(exc.code, int) else 0
(buf_out.getvalue(), buf_err.getvalue(), exit_code)
`);
  const [stdout, stderr, exitCode] = result.toJs();
  result.destroy?.();
  const output = `${stdout || ''}${stdout && stderr && !String(stdout).endsWith('\n') ? '\n' : ''}${stderr || ''}`.trimEnd();

  // Generate a certificate-enabled run after success, then return its contents if Kurt wrote one.
  let certificate = null;
  if (exitCode === 0) {
    await pyodide.runPythonAsync(`
import sys, runpy, io, contextlib
sys.argv = ['kurt.py', '-r', '${Number(indent)}', '/play/proof.kurt']
with contextlib.redirect_stdout(io.StringIO()), contextlib.redirect_stderr(io.StringIO()):
    try: runpy.run_path('/kurt.py', run_name='__main__')
    except SystemExit: pass
`);
    try { certificate = pyodide.FS.readFile('/play/proof.kurtc', { encoding: 'utf8' }); } catch {}
  }
  postMessage({ type: 'result', output, exitCode, certificate });
}

self.onmessage = async ({ data }) => {
  if (data.type !== 'run' || !pyodide) return;
  try { await runProof(data); }
  catch (error) { postMessage({ type: 'error', message: error?.message || String(error) }); }
};
initialize().catch(error => postMessage({ type: 'error', message: error?.message || String(error) }));
