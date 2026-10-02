const $ = selector => document.querySelector(selector);
const editor = $('#editor');
const editorHighlight = $('#editorHighlight');
const output = $('#output');
const outputPanel = $('#outputPanel');
const runBtn = $('#runBtn');
const cancelBtn = $('#cancelBtn');
const statusEl = $('#status');
const examplesContainer = $('#examplesContainer');
const DEFAULT_PROOF = '; simple modus ponens proof\nuse A implies B\nuse A\nB\n';
const DRAFT_KEY = 'kurt.draft';
const SETTINGS_KEY = 'kurt.settings';
let worker, ready = false, running = false, currentFilename = 'proof.kurt';
let replacements = {}, language = {}, lastCertificate = null, lastOutputText = '', saveTimer;

function setStatus(message) { statusEl.textContent = message; }
function setRunning(value) {
  running = value;
  runBtn.disabled = value || !ready;
  cancelBtn.classList.toggle('hidden', !value);
}
function spawnWorker() {
  ready = false;
  setRunning(false);
  setStatus('Loading Kurt runtime…');
  worker = new Worker('kurt-worker.js');
  worker.onmessage = async ({ data }) => {
    if (data.type === 'ready') {
      ready = true; setRunning(false);
      const hash = await runtimeFingerprint();
      $('#version').textContent = `Kurt ${data.version} · ${hash}`;
      setStatus('Ready');
    } else if (data.type === 'result') {
      lastCertificate = data.certificate;
      $('#certificateBtn').disabled = !lastCertificate;
      showOutput(data.output || (data.exitCode ? `Exited with code ${data.exitCode}` : 'Proof checked.'));
      setStatus(data.exitCode ? 'Proof rejected' : 'Proof checked');
      setRunning(false);
    } else if (data.type === 'error') {
      showOutput(`Runtime error: ${data.message}`); setStatus('Runtime error'); setRunning(false);
    }
  };
  worker.onerror = event => { showOutput(`Worker error: ${event.message}`); setStatus('Worker failed'); setRunning(false); };
}
async function runtimeFingerprint() {
  try {
    const bytes = await fetch('kurt.py', { cache: 'no-store' }).then(r => r.arrayBuffer());
    const digest = new Uint8Array(await crypto.subtle.digest('SHA-256', bytes));
    return [...digest].slice(0, 6).map(n => n.toString(16).padStart(2, '0')).join('');
  } catch { return 'fingerprint unavailable'; }
}
function cancelRun() {
  if (!running) return;
  worker.terminate(); setRunning(false); setStatus('Cancelled'); showOutput('Run cancelled.'); spawnWorker();
}
function runProof() {
  if (!ready || running) return;
  lastCertificate = null; $('#certificateBtn').disabled = true;
  outputPanel.classList.remove('hidden'); output.textContent = '';
  setRunning(true); setStatus('Checking proof…');
  worker.postMessage({ type: 'run', code: editor.value, indent: settings().indent });
}

function settings() {
  try { return { fontSize: 15, indent: 40, ...JSON.parse(localStorage.getItem(SETTINGS_KEY) || '{}') }; }
  catch { return { fontSize: 15, indent: 40 }; }
}
function updateSettings(patch) {
  const next = { ...settings(), ...patch };
  localStorage.setItem(SETTINGS_KEY, JSON.stringify(next));
  document.documentElement.style.setProperty('--code-font-size', `${next.fontSize}px`);
  $('#indentLabel').textContent = next.indent; $('#indentSlider').value = next.indent;
  renderEditorHighlight();
}
function persistDraft() {
  clearTimeout(saveTimer);
  saveTimer = setTimeout(() => localStorage.setItem(DRAFT_KEY, JSON.stringify({ code: editor.value, filename: currentFilename })), 250);
}
function setEditor(code, filename = 'proof.kurt') {
  editor.value = code; currentFilename = filename; renderEditorHighlight(); persistDraft();
}

function encodeShare(text) {
  const bytes = new TextEncoder().encode(text);
  let binary = ''; bytes.forEach(byte => { binary += String.fromCharCode(byte); });
  return btoa(binary).replace(/\+/g, '-').replace(/\//g, '_').replace(/=+$/, '');
}
function decodeShare(value) {
  const binary = atob(value.replace(/-/g, '+').replace(/_/g, '/'));
  return new TextDecoder().decode(Uint8Array.from(binary, c => c.charCodeAt(0)));
}
async function shareProof() {
  const url = new URL(location.href); url.hash = `proof=${encodeShare(editor.value)}`;
  history.replaceState(null, '', url);
  try { await navigator.clipboard.writeText(url.href); setStatus('Share link copied'); }
  catch { prompt('Copy this proof link:', url.href); }
}
function loadInitialDraft() {
  const shared = location.hash.match(/^#proof=(.+)$/);
  if (shared) { try { return setEditor(decodeShare(shared[1]), 'shared-proof.kurt'); } catch {} }
  try { const draft = JSON.parse(localStorage.getItem(DRAFT_KEY)); if (draft?.code) return setEditor(draft.code, draft.filename); } catch {}
  setEditor(DEFAULT_PROOF);
}

function download(name, text, type = 'text/plain;charset=utf-8') {
  const link = document.createElement('a');
  link.href = URL.createObjectURL(new Blob([text], { type })); link.download = name; link.click();
  setTimeout(() => URL.revokeObjectURL(link.href), 0);
}
function expandReplacement() {
  const caret = editor.selectionStart;
  const trigger = editor.value[caret - 1];
  if (!trigger || /[A-Za-z0-9]/.test(trigger)) return;
  const beforeTrigger = editor.value.slice(0, caret - 1);
  const match = beforeTrigger.match(/(\\[A-Za-z]+)$/);
  if (!match || !replacements[match[1]]) return;
  const start = caret - 1 - match[1].length;
  const trailing = trigger === '\n' ? '\n' : (trigger === ' ' ? '' : trigger);
  editor.value = editor.value.slice(0, start) + replacements[match[1]] + trailing + editor.value.slice(caret);
  const next = start + replacements[match[1]].length + trailing.length;
  editor.setSelectionRange(next, next);
}
function insertAtCursor(text) {
  const start = editor.selectionStart, end = editor.selectionEnd;
  editor.setRangeText(text, start, end, 'end'); editor.focus(); renderEditorHighlight(); persistDraft();
}

async function loadMetadata() {
  [replacements, language] = await Promise.all([
    fetch('replacements.json').then(r => r.json()), fetch('language.json').then(r => r.json())
  ]);
  buildGrammar(); buildSymbolBar();
}
let grammar = {};
function wordRegex(words) { return new RegExp(`\\b(?:${words.map(w => w.replace(/[.*+?^${}()|[\]\\]/g, '\\$&')).join('|')})\\b`, 'g'); }
function buildGrammar() {
  grammar = {
    declaration: wordRegex(language.declarations || []),
    command: wordRegex([...(language.commands || []), ...(language.helpers || [])]),
    constant: wordRegex(language.constants || []),
    variable: /(?<![A-Za-z0-9_])[%$][A-Za-z0-9_]+/g,
    number: /(?<![A-Za-z0-9_])[0-9]+(?:\.[0-9]+)?(?![A-Za-z0-9_])/g
  };
}
function escapeHtml(text) { return text.replace(/&/g, '&amp;').replace(/</g, '&lt;').replace(/>/g, '&gt;'); }
function highlightLine(line) {
  const safe = escapeHtml(line); let quoted = false, commentAt = -1;
  for (let i = 0; i < safe.length; i++) { if (safe[i] === '"') quoted = !quoted; if (!quoted && safe[i] === ';') { commentAt = i; break; } }
  const code = commentAt < 0 ? safe : safe.slice(0, commentAt), comment = commentAt < 0 ? '' : safe.slice(commentAt);
  let last = 0, pieces = [], match, strings = /".*?"/g;
  while ((match = strings.exec(code))) { pieces.push(colorCode(code.slice(last, match.index))); pieces.push(`<span class="tok-string">${match[0]}</span>`); last = match.index + match[0].length; }
  pieces.push(colorCode(code.slice(last)));
  if (comment) pieces.push(`<span class="tok-comment">${comment}</span>`);
  return pieces.join('') || '\u200b';
}
function colorCode(text) {
  return text.replace(grammar.declaration, m => `<span class="tok-kw1">${m}</span>`)
    .replace(grammar.command, m => `<span class="tok-kw2">${m}</span>`)
    .replace(grammar.constant, m => `<span class="tok-kw3">${m}</span>`)
    .replace(grammar.variable, m => `<span class="tok-variable">${m}</span>`)
    .replace(grammar.number, m => `<span class="tok-number">${m}</span>`);
}
function renderEditorHighlight() {
  editorHighlight.innerHTML = editor.value.split('\n').map(highlightLine).join('\n') || '&nbsp;'; syncScroll();
}
function syncScroll() { editorHighlight.scrollTop = editor.scrollTop; editorHighlight.scrollLeft = editor.scrollLeft; }
function showOutput(text) {
  lastOutputText = String(text || '');
  outputPanel.classList.remove('hidden'); output.innerHTML = '';
  const lines = String(text || '').split('\n'); let pendingLine = null;
  lines.forEach(line => {
    const found = line.match(/File `[^`]+`, line (\d+):/); if (found) pendingLine = Number(found[1]);
    const row = document.createElement(pendingLine ? 'button' : 'span'); row.className = pendingLine ? 'output-line diagnostic' : 'output-line';
    row.innerHTML = highlightLine(line).replace(/\b(\w+Error)\b/g, '<span class="tok-err">$1</span>').replace(/\bProof checked\.?/g, '<span class="tok-ok">$&</span>');
    if (pendingLine) { const target = pendingLine; row.title = `Go to line ${target}`; row.onclick = () => goToLine(target); if (!line.trim()) pendingLine = null; }
    output.append(row);
  });
}
function goToLine(line) {
  const starts = [0]; for (let i = 0; i < editor.value.length; i++) if (editor.value[i] === '\n') starts.push(i + 1);
  const position = starts[Math.max(0, Math.min(line - 1, starts.length - 1))]; editor.focus(); editor.setSelectionRange(position, position); editor.scrollTop = Math.max(0, (line - 3) * parseFloat(getComputedStyle(editor).lineHeight));
}

function buildSymbolBar() {
  const preferred = ['∀','∃','⇒','⇔','¬','∧','∨','⊥','∈','∉','⊆','∪','∩','≤','≥','≠','∞'];
  const bar = $('#symbolBar'); bar.innerHTML = '';
  preferred.forEach(symbol => { const button = document.createElement('button'); button.className = 'symbol'; button.textContent = symbol; button.type = 'button'; button.onclick = () => insertAtCursor(symbol); bar.append(button); });
}
async function listDirectory(path) {
  try { const data = await fetch(`/__list?path=${encodeURIComponent(path)}`).then(r => r.json()); const entries = [...data.dirs, ...data.files]; if (entries.length) return entries; } catch {}
  const manifest = await fetch('manifest.json').then(r => r.json());
  if (path === 'proofs/') return Object.keys(manifest.proofs).map(x => `${x}/`);
  if (path === 'theories/') return manifest.theories;
  const folder = path.match(/^proofs\/([^/]+)\/$/)?.[1]; return folder ? manifest.proofs[folder] || [] : [];
}
async function buildExamplesUI() {
  const folders = (await listDirectory('proofs/')).filter(x => x.endsWith('/'));
  for (const folder of folders) await createMenu(folder.slice(0, -1), `proofs/${folder}`);
  await createMenu('theories', 'theories/');
}
async function createMenu(label, path) {
  const files = (await listDirectory(path)).filter(x => x.endsWith('.kurt')); if (!files.length) return;
  const wrapper = document.createElement('div'); wrapper.className = 'menu-wrapper';
  const button = document.createElement('button'); button.className = 'btn small'; button.textContent = label;
  const menu = document.createElement('div'); menu.className = 'dropdown-menu hidden';
  files.forEach(file => { const item = document.createElement('button'); item.className = 'item'; item.textContent = file;
    item.onclick = async () => { const response = await fetch(`${path}${file}`); if (!response.ok) return setStatus('Could not load example'); setEditor(await response.text(), file); menu.classList.add('hidden'); setStatus('Ready'); };
    menu.append(item);
  });
  button.onclick = event => {
    event.stopPropagation();
    document.querySelectorAll('.dropdown-menu').forEach(x => x !== menu && x.classList.add('hidden'));
    menu.classList.toggle('hidden');
    if (!menu.classList.contains('hidden')) {
      // fit the menu into the window below its button, so a long one scrolls instead of running off the screen
      menu.style.maxHeight = `${Math.max(160, window.innerHeight - menu.getBoundingClientRect().top - 12)}px`;
      menu.scrollTop = 0;
    }
  };
  wrapper.append(button, menu); examplesContainer.append(wrapper);
}

function setupUI() {
  loadInitialDraft(); const saved = settings(); updateSettings(saved);
  editor.addEventListener('input', () => { expandReplacement(); renderEditorHighlight(); persistDraft(); }); editor.addEventListener('scroll', syncScroll);
  editor.addEventListener('keydown', event => { if ((event.ctrlKey || event.metaKey) && event.key === 'Enter') { event.preventDefault(); runProof(); } });
  runBtn.onclick = runProof; cancelBtn.onclick = cancelRun; $('#shareBtn').onclick = shareProof;
  $('#copyBtn').onclick = async () => { await navigator.clipboard.writeText(lastOutputText); setStatus('Output copied'); };
  $('#clearBtn').onclick = () => { output.textContent = ''; outputPanel.classList.add('hidden'); };
  $('#outputDownloadBtn').onclick = () => download('kurt-output.txt', lastOutputText);
  $('#certificateBtn').onclick = () => lastCertificate && download('proof.kurtc', lastCertificate, 'application/json');
  $('#saveBtn').onclick = () => download(currentFilename.endsWith('.kurt') ? currentFilename : `${currentFilename}.kurt`, editor.value);
  $('#loadBtn').onclick = () => { const input = document.createElement('input'); input.type = 'file'; input.accept = '.kurt,text/plain'; input.onchange = async () => input.files[0] && setEditor(await input.files[0].text(), input.files[0].name); input.click(); };
  $('#indentBtn').onclick = () => $('#indentPopover').classList.toggle('hidden');
  $('#indentSlider').oninput = event => updateSettings({ indent: Number(event.target.value) });
  document.addEventListener('click', event => { if (!event.target.closest('.menu-wrapper')) document.querySelectorAll('.dropdown-menu').forEach(x => x.classList.add('hidden')); });
  window.addEventListener('keydown', event => { if (!(event.ctrlKey || event.metaKey)) return; if (['+','=','-','0'].includes(event.key)) { event.preventDefault(); const size = event.key === '0' ? 15 : Math.max(10, Math.min(24, settings().fontSize + (event.key === '-' ? -1 : 1))); updateSettings({ fontSize: size }); } });
}

window.addEventListener('DOMContentLoaded', async () => {
  setupUI();
  try { await loadMetadata(); renderEditorHighlight(); await buildExamplesUI(); spawnWorker(); }
  catch (error) { setStatus('Initialization failed'); showOutput(error.message); }
  if ('serviceWorker' in navigator) navigator.serviceWorker.register('service-worker.js').catch(console.warn);
});
