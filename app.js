// Kurt Playground JS: loads Pyodide, mounts kurt.py, and runs proofs client-side.

let pyodide = null;
let kurtPyCode = null;
let theoriesSynced = false;
let currentFilename = 'proof.kurt';
let replacements = {};

const $ = (sel) => document.querySelector(sel);
const editor = $('#editor');
const output = $('#output');
const outputPanel = $('#outputPanel');
const runBtn = $('#runBtn');
const copyBtn = $('#copyBtn');
const clearBtn = $('#clearBtn');
const statusEl = $('#status');
const examplesContainer = $('#examplesContainer');
const editorHighlight = $('#editorHighlight');
const loadBtn = $('#loadBtn');
const saveBtn = $('#saveBtn');
// no help modal

// A small, built-in fallback for kurt.py if fetching from the workspace fails.
// This fallback prints a banner and echoes input lines; replace when real kurt.py is available.
const FALLBACK_KURT_PY = `#!/usr/bin/env python3
import sys
banner = "This is Kurt, Browser Playground (fallback)\n"
def run(path):
    print(banner, end='')
    try:
        with open(path, 'r', encoding='utf-8') as f:
            for i, line in enumerate(f, 1):
                line = line.rstrip('\n')
                if not line or line.strip().startswith(';'):
                    continue
                print(f"{line}                                             ; {i} echo")
        print("Proof checked.")
    except Exception as e:
        print(f"Error: {e}", file=sys.stderr)
        sys.exit(1)

def main(argv):
    if len(argv) >= 2:
        run(argv[1])
    else:
        print(banner, end='')
        print("Type your proof in the editor and press Run.")

if __name__ == '__main__':
    main(sys.argv)
`;

function setStatus(msg) {
  statusEl.textContent = msg;
}

function showOutput(text) {
  if (!text) return;
  outputPanel.classList.remove('hidden');
  output.innerHTML = highlightOutput(text);
}

function appendOutput(text) {
  outputPanel.classList.remove('hidden');
  output.textContent += text;
}

function clearOutput() {
  // Clear both raw text and any highlighted HTML
  output.textContent = '';
  output.innerHTML = '';
  // Hide the output panel until next run
  outputPanel.classList.add('hidden');
}

function setRunning(running) {
  runBtn.disabled = running || !kurtPyCode || !pyodide;
  runBtn.textContent = running ? 'Running…' : 'Run';
}

async function loadKurtPy() {
  // Try to fetch kurt.py from a sibling path (when hosted alongside this site).
  // If unavailable, use the fallback.
  try {
    const res = await fetch('kurt.py', { cache: 'no-store' });
    if (res.ok) {
      return await res.text();
    }
  } catch (e) {
    // ignore and fallback
  }
  return FALLBACK_KURT_PY;
}

async function init() {
  try {
    setStatus('Loading Python runtime…');
    pyodide = await loadPyodide({ indexURL: 'https://cdn.jsdelivr.net/pyodide/v0.26.2/full/' });
    setStatus('Fetching kurt.py…');
    kurtPyCode = await loadKurtPy();

    // Write kurt.py into Pyodide FS
    pyodide.FS.writeFile('/kurt.py', kurtPyCode, { encoding: 'utf8' });

    // Ensure a working directory
    try { pyodide.FS.mkdir('/play'); } catch {}
    pyodide.FS.chdir('/play');

    // Fire-and-forget: load replacements map
    loadReplacements();

    setStatus('Ready');
    runBtn.disabled = false;
    // Populate example pickers if proofs/ exists
    await buildExamplesUI();
  } catch (err) {
    console.error(err);
    setStatus('Failed to initialize');
    showOutput(String(err));
  }
}

async function loadReplacements() {
  try {
    const res = await fetch('replacements.json', { cache: 'no-store' });
    if (res.ok) {
      const json = await res.json();
      if (json && typeof json === 'object') {
        replacements = json;
        // console.log('Loaded replacements', replacements);
      }
    }
  } catch (e) {
    // ignore; feature is optional
  }
}

async function runProof() {
  if (!pyodide) return;
  setRunning(true);
  clearOutput();

  const code = editor.value ?? '';
  // Save code into a temp file
  const tmpName = `proof_${Date.now()}.kurt`;
  try {
    // Ensure support files like theories/ are available to the Python FS
    await syncTheoriesToFS();
    pyodide.FS.writeFile(tmpName, code, { encoding: 'utf8' });
  } catch (e) {
    setRunning(false);
    showOutput('Failed to write proof file: ' + e);
    return;
  }

  try {
    const pyResult = await pyodide.runPythonAsync(`
import sys, runpy, io, contextlib
sys.argv = ['kurt.py', '${tmpName}']
buf_out = io.StringIO()
buf_err = io.StringIO()
with contextlib.redirect_stdout(buf_out), contextlib.redirect_stderr(buf_err):
    try:
        runpy.run_path('/kurt.py', run_name='__main__')
    except SystemExit as e:
        code = e.code if isinstance(e.code, int) else 0
        if code != 0:
            print(f"Exited with code {code}", file=sys.stderr)
(buf_out.getvalue(), buf_err.getvalue())
`);
    let pair;
    if (pyResult && typeof pyResult.toJs === 'function') {
      pair = pyResult.toJs();
    } else {
      pair = pyResult;
    }
    const outStr = (pair && pair[0]) ? String(pair[0]) : '';
    const errStr = (pair && pair[1]) ? String(pair[1]) : '';
    const normOut = outStr.replace(/\r\n/g, '\n').replace(/\r/g, '\n');
    const normErr = errStr.replace(/\r\n/g, '\n').replace(/\r/g, '\n');
    const combined = (normOut + (normErr ? ((normOut && !normOut.endsWith('\n')) ? '\n' : '') + normErr : '')).trimEnd();
    if (combined) {
      showOutput(combined);
    } else {
      showOutput('');
      setStatus('Ran with no output');
    }
  } catch (e) {
    const msg = (e && e.message) ? e.message : String(e);
    showOutput(msg);
  }
  setRunning(false);
}

function setupUI() {
  // Prefill sample proof
  editor.value = `; simple modus ponens proof\nbool A, B\nuse A implies B\nuse A\nB\n`;
  renderEditorHighlight();

  runBtn.addEventListener('click', runProof);
  copyBtn.addEventListener('click', async () => {
    const txt = output.textContent;
    try {
      await navigator.clipboard.writeText(txt);
      setStatus('Output copied');
      setTimeout(() => setStatus('Ready'), 1200);
    } catch {
      setStatus('Copy failed');
      setTimeout(() => setStatus('Ready'), 1200);
    }
  });
  if (clearBtn) {
    clearBtn.addEventListener('click', () => {
      clearOutput();
      // Keep panel visible but empty
      statusEl.textContent = 'Output cleared';
      setTimeout(() => setStatus('Ready'), 1000);
    });
  }

  // Run on Cmd/Ctrl+Enter
  editor.addEventListener('keydown', (e) => {
    const isMac = navigator.platform.toLowerCase().includes('mac');
    const accel = isMac ? e.metaKey : e.ctrlKey;
    if (accel && e.key === 'Enter') {
      e.preventDefault();
      runBtn.click();
    }
  });
  editor.addEventListener('input', renderEditorHighlight);
  editor.addEventListener('scroll', syncScroll);
  // Keep overlay sized with editor
  const ro = new ResizeObserver(() => syncScroll());
  ro.observe(editor);

  // Replacement mechanism similar to VS Code extension
  let lastKey = null;
  let caretBefore = 0;
  editor.addEventListener('keydown', (e) => {
    lastKey = e.key;
    caretBefore = editor.selectionStart;
  });
  editor.addEventListener('input', () => {
    maybeApplyReplacement(lastKey, caretBefore);
    // reset so paste/composition won't get processed repeatedly
    lastKey = null;
  });
}

window.addEventListener('DOMContentLoaded', () => {
  setupUI();
  init();
});

// Discover subfolders and build compact dropdown buttons
async function listDirectory(path) {
  // 1) Try dev server JSON endpoint (available when running server.py)
  try {
    const res = await fetch(`/__list?path=${encodeURIComponent(path)}`, { cache: 'no-store' });
    if (res.ok) {
      const data = await res.json();
      const list = [...(data.dirs || []), ...(data.files || [])];
      if (list.length) return list;
    }
  } catch {}

  // 2) Fallback for static hosting (e.g., GitHub Pages): use manifest.json
  try {
    const mres = await fetch('manifest.json', { cache: 'no-store' });
    if (!mres.ok) return [];
    const manifest = await mres.json();
    const fromManifest = resolveManifestListing(manifest, path);
    return fromManifest;
  } catch {
    return [];
  }
}

function isAlphaNum(ch) {
  return /^[a-zA-Z0-9]$/.test(ch);
}

function maybeApplyReplacement(triggerKey, caretPosBefore) {
  if (!replacements || !editor) return;
  // Only act on a single-character trigger keys or Enter
  let triggerChar = null;
  if (triggerKey === 'Enter') triggerChar = '\n';
  else if (triggerKey === ' ') triggerChar = ' ';
  else if (triggerKey && triggerKey.length === 1) triggerChar = triggerKey;
  else return;

  if (isAlphaNum(triggerChar)) return; // ignore alphanumerics

  const text = editor.value;
  // After the input event, the caret is after the inserted char
  const caret = editor.selectionStart;
  // We expect that exactly one char was inserted; indexBefore points to the position of that char
  const indexBefore = Math.max(0, caret - 1);

  // Compute line start and textBefore (up to, but not including, the trigger char)
  const lineStart = text.lastIndexOf('\n', indexBefore - 1) + 1;
  const textBefore = text.slice(lineStart, indexBefore);

  const m = textBefore.match(/(\\[a-zA-Z]+)$/);
  if (!m) return;
  const matchedCommand = m[1];
  const replacement = replacements[matchedCommand];
  if (!replacement) return;

  // Determine replacement range in the whole text
  const matchStartInLine = textBefore.length - matchedCommand.length;
  const startIndex = lineStart + matchStartInLine;
  let endIndex;
  if (triggerChar === ' ' || triggerChar === '\n') {
    // Also remove the space/newline we just typed
    endIndex = indexBefore + 1;
  } else {
    endIndex = indexBefore; // keep punctuation etc.
  }

  const shouldKeepTrigger = triggerChar !== ' ' && triggerChar !== '\n' && triggerChar !== '\\';
  let finalText = replacement + (shouldKeepTrigger ? triggerChar : '');

  // Build new editor value
  const newVal = text.slice(0, startIndex) + finalText + text.slice(endIndex);
  editor.value = newVal;
  renderEditorHighlight();

  // Set caret position
  let newCaret = startIndex + finalText.length;
  if (triggerChar === '\n') {
    // Manually insert a newline after the replacement
    const withNl = newVal.slice(0, newCaret) + '\n' + newVal.slice(newCaret);
    editor.value = withNl;
    renderEditorHighlight();
    newCaret += 1;
  }
  editor.selectionStart = editor.selectionEnd = newCaret;
}

function resolveManifestListing(manifest, path) {
  // Normalize path to ensure trailing slash for directories
  const p = path.endsWith('/') ? path : path + '/';
  const proofs = manifest.proofs || {};
  const theories = manifest.theories || [];

  // List top-level of proofs/ -> return subfolder names with trailing slash
  if (p === 'proofs/') {
    const subfolders = Object.keys(proofs);
    return subfolders.map((s) => s.replace(/\/$/, '') + '/');
  }
  // List specific proofs subfolder e.g., proofs/examples/
  if (p.startsWith('proofs/')) {
    const parts = p.split('/').filter(Boolean); // ["proofs", "examples"]
    if (parts.length === 2) {
      const folder = parts[1];
      const files = proofs[folder] || [];
      return files;
    }
  }
  // List theories/
  if (p === 'theories/') {
    return theories;
  }
  return [];
}

async function buildExamplesUI() {
  if (!examplesContainer) return;
  examplesContainer.innerHTML = '';

  // Helper to create a menu button for a directory
  const createMenu = async (label, dirPath) => {
    const entries = await listDirectory(dirPath);
    const kurtFiles = entries.filter(n => n.toLowerCase().endsWith('.kurt'));
    if (kurtFiles.length === 0) return;

    const wrapper = document.createElement('div');
    wrapper.className = 'menu-wrapper';

    const btn = document.createElement('button');
    btn.className = 'btn small';
    btn.type = 'button';
    btn.innerHTML = `<span>${label}</span>`;

    const menu = document.createElement('div');
    menu.className = 'dropdown-menu hidden';
    for (const f of kurtFiles) {
      const item = document.createElement('button');
      item.className = 'item';
      item.type = 'button';
      item.textContent = f;
      item.addEventListener('click', async () => {
        const path = `${dirPath}${f}`;
        try {
          setStatus(`Loading ${path}…`);
          const res = await fetch(path, { cache: 'no-store' });
          const txt = await res.text();
          editor.value = txt;
          renderEditorHighlight();
          currentFilename = f.replace(/[\\\/]+/g, '').trim() || 'proof.kurt';
          setStatus('Ready');
        } catch (err) {
          setStatus('Failed to load example');
        } finally {
          menu.classList.add('hidden');
        }
      });
      menu.appendChild(item);
    }

    // Toggle menu
    btn.addEventListener('click', (e) => {
      const wasHidden = menu.classList.contains('hidden');
      document.querySelectorAll('.dropdown-menu').forEach(el => el.classList.add('hidden'));
      if (wasHidden) menu.classList.remove('hidden');
    });

    // Close on outside click
    document.addEventListener('click', (e) => {
      if (!wrapper.contains(e.target)) menu.classList.add('hidden');
    });

    wrapper.appendChild(btn);
    wrapper.appendChild(menu);
    examplesContainer.appendChild(wrapper);
  };

  // Upload: open file picker and replace editor content
  loadBtn.addEventListener('click', async () => {
    const input = document.createElement('input');
    input.type = 'file';
    input.accept = '.kurt,text/plain';
    input.onchange = async () => {
      const file = input.files && input.files[0];
      if (!file) return;
      try {
        const text = await file.text();
        editor.value = text;
        renderEditorHighlight();
        currentFilename = (file.name || 'proof.kurt').replace(/[\\\/]+/g, '').trim();
        setStatus(`Uploaded ${file.name}`);
      } catch (e) {
        setStatus('Failed to upload file');
      }
    };
    input.click();
  });
  // Download: save current editor content as a .kurt file
  saveBtn.addEventListener('click', () => {
    const blob = new Blob([editor.value || ''], { type: 'text/plain;charset=utf-8' });
    const url = URL.createObjectURL(blob);
    const a = document.createElement('a');
    a.href = url;
    a.download = currentFilename && currentFilename.toLowerCase().endsWith('.kurt') ? currentFilename : (currentFilename || 'proof.kurt') + '.kurt';
    document.body.appendChild(a);
    a.click();
    a.remove();
    URL.revokeObjectURL(url);
    setStatus(`Downloaded ${a.download}`);
  });
  // Discover proofs subfolders
  const rootEntries = await listDirectory('proofs/');
  const subfolders = rootEntries.filter(e => /\/$/.test(e)).map(e => e.replace(/\/$/, ''));

  // 1) examples
  if (subfolders.includes('examples')) {
    await createMenu('examples', 'proofs/examples/');
  }
  // 2) tutorial
  if (subfolders.includes('tutorial')) {
    await createMenu('tutorial', 'proofs/tutorial/');
  }
  // 3) any other subfolders (sorted), excluding examples/tutorial
  const others = subfolders.filter(s => s !== 'examples' && s !== 'tutorial').sort();
  for (const folder of others) {
    await createMenu(folder, `proofs/${folder}/`);
  }
  // 4) theories at the end
  await createMenu('theories', 'theories/');
}

// --- Sync support folders into Pyodide FS ---
async function syncTheoriesToFS() {
  if (theoriesSynced) return;
  try {
    await mirrorFolderToFS('theories/', '/theories/');
    theoriesSynced = true;
  } catch (e) {
    // Non-fatal: if theories/ is missing, run may fail later with a clear error
    console.warn('Failed to sync theories/:', e);
  }
}

async function mirrorFolderToFS(webPath, fsPath) {
  // Ensure destination directory exists
  ensureFsDir(fsPath);
  const entries = await listDirectory(webPath);
  // Separate dirs and files based on trailing slash
  const dirs = entries.filter(e => /\/$/.test(e));
  const files = entries.filter(e => !/\/$/.test(e));
  // Write files
  for (const file of files) {
    const url = `${webPath}${file}`;
    const dest = fsPath + file;
    const resp = await fetch(url, { cache: 'no-store' });
    if (!resp.ok) continue;
    const text = await resp.text();
    pyodide.FS.writeFile(dest, text, { encoding: 'utf8' });
  }
  // Recurse into subdirectories
  for (const dir of dirs) {
    await mirrorFolderToFS(webPath + dir, fsPath + dir);
  }
}

function ensureFsDir(path) {
  const parts = path.split('/').filter(Boolean);
  let current = '/';
  for (const p of parts) {
    current += p + '/';
    try {
      pyodide.FS.mkdir(current);
    } catch (e) {
      // exists
    }
  }
}

// --- Syntax highlighting ---
const grammar = {
  comment: /;.*$/gm,
  string: /".*?"/g,
  kw1: /\b(?:var|const|infix|postfix|prefix|brackets|arity|bindop|chain|flat|sym|bool|alias)\b/g,
  kw2: /\b(?:load|use|assume|show|def|fix|pick|proof|qed|thus|with|parse|tokenize|format|level|mode|context|trail|syntax|theory|implications|help|break)\b/g,
  kw3: /\b(?:contradiction|true|false)\b/g,
  todo: /\b(?:todo)\b/g,
};

function escapeHtml(s) {
  return s.replace(/&/g, '&amp;').replace(/</g, '&lt;').replace(/>/g, '&gt;');
}

function renderEditorHighlight() {
  if (!editorHighlight) return;
  const src = editor.value || '';
  // Process line by line to keep comments to end-of-line
  const lines = src.split(/\n/);
  const out = lines.map((line) => highlightLine(line)).join('\n');
  editorHighlight.innerHTML = out || '&nbsp;';
  syncScroll();
}

function highlightLine(line) {
  if (!line) return '\u200B';
  const safe = escapeHtml(line);
  // Find comment start (;) not inside a string
  let inString = false;
  let commentIdx = -1;
  for (let i = 0; i < safe.length; i++) {
    const ch = safe[i];
    if (ch === '"') inString = !inString;
    if (!inString && ch === ';') { commentIdx = i; break; }
  }
  const codePart = commentIdx >= 0 ? safe.slice(0, commentIdx) : safe;
  const commentPart = commentIdx >= 0 ? safe.slice(commentIdx) : '';

  // Split codePart by strings so we can avoid keywording inside strings
  const stringRe = /\".*?\"/g;
  const segments = [];
  let last = 0;
  let m;
  while ((m = stringRe.exec(codePart))) {
    if (m.index > last) segments.push({ type: 'code', text: codePart.slice(last, m.index) });
    segments.push({ type: 'string', text: m[0] });
    last = m.index + m[0].length;
  }
  if (last < codePart.length) segments.push({ type: 'code', text: codePart.slice(last) });

  const coloredCode = segments.map(seg => {
    if (seg.type === 'string') {
      return `<span class="tok-string">${seg.text}</span>`;
    }
    return seg.text
      .replace(grammar.kw1, (mm) => `<span class="tok-kw1">${mm}</span>`)
      .replace(grammar.kw2, (mm) => `<span class="tok-kw2">${mm}</span>`)
      .replace(grammar.kw3, (mm) => `<span class="tok-kw3">${mm}</span>`)
      .replace(grammar.todo, (mm) => `<span class="tok-todo">${mm}</span>`);
  }).join('');

  const commentHtml = commentPart ? `<span class=\"tok-comment\">${commentPart}</span>` : '';
  return coloredCode + commentHtml;
}

function syncScroll() {
  if (!editorHighlight) return;
  editorHighlight.scrollTop = editor.scrollTop;
  editorHighlight.scrollLeft = editor.scrollLeft;
  // Match height to prevent wrap differences
  editorHighlight.style.height = `${editor.clientHeight}px`;
  editorHighlight.style.width = `${editor.clientWidth}px`;
}

function highlightOutput(text) {
  const lines = (text || '').split(/\n/);
  return lines.map((line) => {
    // First, base highlighting
    let html = highlightLine(line);
    // Then success and error emphasis on the non-comment portion
    // Split off trailing comment span if present to avoid coloring inside
    const parts = html.split(/(<span class=\"tok-comment\">.*<\/span>)$/);
    let head = parts[0] || '';
    const tail = parts[1] || '';
    // Success phrase
    head = head.replace(/\bProof checked\.?\b/, (m) => `<span class="tok-ok">${m}</span>`);
    // Error words
    head = head.replace(/\b(EvalError|ProofError|ParseError|SyntaxError)\b/g, (m) => `<span class="tok-err">${m}</span>`);
    return head + tail;
  }).join('\n');
}
