// Kurt Playground JS: loads Pyodide, mounts kurt.py, and runs proofs client-side.

let pyodide = null;
let kurtPyCode = null;
let theoriesSynced = false;
let currentFilename = 'proof.kurt';
let replacements = {};
let initializing = false;
let indentRerunTimer = null; // shared debounce timer for indent-triggered re-runs
let isRunning = false;       // tracks an active run
let rerunQueued = false;     // queue a rerun when changes happen during a run
let lastRunIndent = null;    // remember last indent value used
// code font size controls only; font family is fixed to monospace

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
// Indentation controls
const indentBtn = $('#indentBtn');
const indentLabel = $('#indentLabel');
const indentPopover = $('#indentPopover');
const indentSlider = $('#indentSlider');
// minimal popover now only has a slider
// no font family toggle button
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
  # accept optional -r <indent> before the file path
  args = list(argv[1:])
  file = None
  i = 0
  while i < len(args):
    if args[i] == '-r' and i + 1 < len(args):
      # ignore in fallback
      i += 2
      continue
    file = args[i]
    break
  if file:
    run(file)
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
  // Ensure panel is visible now that we have something to show
  if (outputPanel && outputPanel.classList.contains('hidden')) {
    outputPanel.classList.remove('hidden');
  }
  const nextHtml = highlightOutput(text);
  if (output.innerHTML !== nextHtml) {
    output.innerHTML = nextHtml;
  }
}

function appendOutput(text) {
  outputPanel.classList.remove('hidden');
  output.textContent += text;
}

function clearOutput() {
  // Clear both raw text and any highlighted HTML
  output.textContent = '';
  output.innerHTML = '';
  // Keep the output panel visible to avoid layout reflow flicker
}

function setRunning(running) {
  runBtn.disabled = running || !kurtPyCode || !pyodide;
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
  if (initializing) return;
  initializing = true;
  try {
    setStatus('Loading Python runtime…');

    // Ensure loadPyodide function exists; if not, try alternate CDN script
    if (typeof loadPyodide !== 'function') {
      await loadPyodideScriptFallback();
    }

    // Attempt primary, then alternate indexURL if needed
    const primaryURL = 'https://cdn.jsdelivr.net/pyodide/v0.26.2/full/';
    const altURL = 'https://cdn.jsdelivr.net/npm/pyodide@0.26.2/full/';
    try {
      pyodide = await loadPyodideWithTimeout(primaryURL, 15000);
    } catch (e1) {
      setStatus('Pyodide slow or blocked; trying alternate CDN…');
      try {
        pyodide = await loadPyodideWithTimeout(altURL, 15000);
      } catch (e2) {
        throw e2 || e1;
      }
    }
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
    // Offer a retry action
    if (statusEl) {
      statusEl.innerHTML = 'Failed to initialize. <a href="#" id="retryInit">Retry</a>';
      const retry = document.getElementById('retryInit');
      if (retry) retry.addEventListener('click', (e) => { e.preventDefault(); initializing = false; init(); });
    }
  }
  initializing = false;
}

async function loadPyodideWithTimeout(indexURL, timeoutMs) {
  setStatus('Loading Python runtime…');
  const timeout = new Promise((_, reject) => setTimeout(() => reject(new Error('Pyodide load timeout')), timeoutMs));
  const load = (async () => await loadPyodide({ indexURL }))();
  return await Promise.race([load, timeout]);
}

async function loadPyodideScriptFallback() {
  // try alternate CDN script if the primary failed to define loadPyodide
  return new Promise((resolve, reject) => {
    const existing = document.querySelector('script[src*="pyodide.js"]');
    // If a pyodide script is already present, just wait a bit more
    if (existing && typeof loadPyodide === 'function') return resolve();
    const script = document.createElement('script');
    script.src = 'https://cdn.jsdelivr.net/npm/pyodide@0.26.2/full/pyodide.js';
    script.async = true;
    script.onload = () => resolve();
    script.onerror = () => reject(new Error('Failed to load alternate Pyodide script'));
    document.head.appendChild(script);
    // Also set a guard timeout
    setTimeout(() => {
      if (typeof loadPyodide === 'function') resolve();
    }, 5000);
  });
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

async function runProof(options = {}) {
  if (!pyodide) return;
  const silent = !!options.silent;
  const currentIndent = getReasonIndent();
  // If a run is in progress, coalesce and run once after it finishes
  if (isRunning) {
    rerunQueued = true;
    return;
  }
  isRunning = true;
  if (!silent) setRunning(true);
  clearOutput();
  if (outputPanel && outputPanel.classList.contains('hidden')) {
    outputPanel.classList.remove('hidden');
  }

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
    const indent = getReasonIndent();
  const pyResult = await pyodide.runPythonAsync(`
import sys, runpy, io, contextlib
sys.argv = ['kurt.py', '-r', '${indent}', '${tmpName}']
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
      if (!silent) setStatus('Ran with no output');
    }
  } catch (e) {
    const msg = (e && e.message) ? e.message : String(e);
    showOutput(msg);
  }
  lastRunIndent = currentIndent;
  isRunning = false;
  if (!silent) setRunning(false);
  // If a rerun was queued during this run, or the indent changed again, run once more silently
  if (rerunQueued || getReasonIndent() !== lastRunIndent) {
    rerunQueued = false;
    scheduleIndentRerun();
  }
}

function setupUI() {
  // Prefill sample proof
  editor.value = `; simple modus ponens proof\nuse A implies B\nuse A\nB\n`;
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
      if (outputPanel && !outputPanel.classList.contains('hidden')) {
        outputPanel.classList.add('hidden');
      }
      // Keep panel visible but empty and minimize status churn
      setStatus('Output cleared');
      setTimeout(() => setStatus('Ready'), 600);
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

  // Remove any residual font toggle button from the DOM (we keep only size shortcuts)
  const toggleBtn = document.getElementById('fontToggle');
  if (toggleBtn && toggleBtn.parentElement) {
    toggleBtn.parentElement.removeChild(toggleBtn);
  }

  // Keyboard shortcuts: Cmd/Ctrl +/- adjust size; Cmd/Ctrl+0 reset
  window.addEventListener('keydown', (e) => {
    const isMac = navigator.platform.toLowerCase().includes('mac');
    const accel = isMac ? e.metaKey : e.ctrlKey;
  if (!accel) return;
    if (e.key === '+' || e.key === '=') {
      e.preventDefault();
      adjustCodeFontSize(1);
    } else if (e.key === '-') {
      e.preventDefault();
      adjustCodeFontSize(-1);
    } else if (e.key === '0') {
      e.preventDefault();
      setCodeFontSize(15);
    } else if (e.key === ']') {
      e.preventDefault();
      adjustReasonIndent(2);
  scheduleIndentRerun();
    } else if (e.key === '[') {
      e.preventDefault();
      adjustReasonIndent(-2);
  scheduleIndentRerun();
    }
  });

  // Indent controls wiring
  initReasonIndentUI();
}

window.addEventListener('DOMContentLoaded', () => {
  try {
    setupUI();
  } catch (e) {
    console.error('UI setup failed:', e);
    setStatus('UI init error; continuing…');
  }
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

function getCurrentCodeFontSize() {
  const root = getComputedStyle(document.documentElement);
  const sz = root.getPropertyValue('--code-font-size').trim();
  const n = parseFloat(sz);
  return Number.isFinite(n) ? n : 13;
}

function setCodeFontSize(px) {
  const clamped = Math.max(10, Math.min(24, Math.round(px)));
  document.documentElement.style.setProperty('--code-font-size', `${clamped}px`);
  // re-render to ensure overlay stays in sync if metrics change
  renderEditorHighlight();
}

function adjustCodeFontSize(delta) {
  setCodeFontSize(getCurrentCodeFontSize() + delta);
}

// --- Reason indent control ---
const INDENT_KEY = 'kurt.reasonIndent';
const INDENT_DEFAULT = 40;
const INDENT_MIN = 20;
const INDENT_MAX = 120;

function getReasonIndent() {
  const v = parseInt(localStorage.getItem(INDENT_KEY) || '', 10);
  if (Number.isFinite(v)) return clampIndent(v);
  return INDENT_DEFAULT;
}

function setReasonIndent(v) {
  const clamped = clampIndent(v);
  localStorage.setItem(INDENT_KEY, String(clamped));
  if (indentLabel) indentLabel.textContent = String(clamped);
  if (indentSlider) indentSlider.value = String(clamped);
}

function clampIndent(v) {
  const n = Math.round(Number(v));
  return Math.max(INDENT_MIN, Math.min(INDENT_MAX, n));
}

function adjustReasonIndent(delta) {
  setReasonIndent(getReasonIndent() + delta);
}

function initReasonIndentUI() {
  // One-time migration: if no value or legacy 86, reset to 40
  const raw = localStorage.getItem(INDENT_KEY);
  const parsed = raw !== null ? parseInt(raw, 10) : NaN;
  if (!Number.isFinite(parsed) || parsed === 86) {
    setReasonIndent(INDENT_DEFAULT);
  } else {
    setReasonIndent(parsed);
  }
  let indentOpenAt = null;
  if (indentBtn && indentPopover) {
    indentBtn.addEventListener('click', (e) => {
      e.stopPropagation();
      if (!indentPopover) return;
      const wasHidden = indentPopover.classList.contains('hidden');
      // Hide other popovers first
      document.querySelectorAll('.popover').forEach(el => el.classList.add('hidden'));
      if (wasHidden) {
        // Opening: record current value
        indentOpenAt = getReasonIndent();
        indentPopover.classList.remove('hidden');
        indentPopover.style.display = 'block';
        console.debug('Indent popover opened');
        // Focus slider for immediate keyboard/drag interaction
        if (indentSlider) {
          try { indentSlider.focus(); } catch {}
        }
      } else {
        // Closing via toggle: run if changed (safety; live updates already run)
        indentPopover.classList.add('hidden');
        indentPopover.style.display = '';
        const changed = indentOpenAt !== null && getReasonIndent() !== indentOpenAt;
        indentOpenAt = null;
        if (changed && !runBtn.disabled) {
          runProof();
        }
      }
    });
    // close on outside click
    document.addEventListener('click', (e) => {
      if (!indentPopover.contains(e.target) && e.target !== indentBtn && !indentBtn.contains(e.target)) {
        const wasVisible = !indentPopover.classList.contains('hidden');
        if (wasVisible) {
          indentPopover.classList.add('hidden');
          indentPopover.style.display = '';
          const changed = indentOpenAt !== null && getReasonIndent() !== indentOpenAt;
          indentOpenAt = null;
          if (changed && !runBtn.disabled) {
            runProof();
          }
        }
      }
    });
    // Prevent clicks within the popover from bubbling to the document handler
    indentPopover.addEventListener('click', (e) => e.stopPropagation());
    indentPopover.addEventListener('mousedown', (e) => e.stopPropagation());
  }
  // Live updates with debounce to avoid rapid re-runs during drag
  if (indentSlider) {
    indentSlider.addEventListener('input', () => {
      setReasonIndent(parseInt(indentSlider.value, 10));
      scheduleIndentRerun();
    });
  }
}

function scheduleIndentRerun() {
  if (indentRerunTimer) clearTimeout(indentRerunTimer);
  indentRerunTimer = setTimeout(() => {
    if (!runBtn.disabled) runProof({ silent: true });
  }, 200);
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
