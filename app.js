const $ = selector => document.querySelector(selector);
const editor = $('#editor');
const editorHighlight = $('#editorHighlight');
const lineNumbers = $('#lineNumbers');
const output = $('#output');
const outputPanel = $('#outputPanel');
const runBtn = $('#runBtn');
const cancelBtn = $('#cancelBtn');
const statusEl = $('#status');
const examplesContainer = $('#examplesContainer');
const DEFAULT_PROOF = '; simple modus ponens proof\nuse A implies B\nuse A\nB\n';
const DRAFT_KEY = 'kurt.draft';
const SETTINGS_KEY = 'kurt.settings';
let worker, ready = false, running = false, currentFilename = 'proof.kurt', currentFolder = null;
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
      shellStarted(data.shell);
    } else if (data.type === 'shell-output') {
      showOutput(`${lastOutputText}\n${shellEcho}\n${(data.output || '').trimEnd()}`.replace(/\n+$/, ''));
      output.scrollTop = output.scrollHeight;
      shellUpdate(data.shell);
    } else if (data.type === 'completions') {
      shellCompleted(data.items, data.line, data.word);
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
// the files that `load` lines name and that are no theory, e.g. the helper of a lesson
// (`load 12-my-theory`): fetched from the folder the proof came from, also what they load
async function loadedFiles(code) {
  if (!currentFolder) return {};
  let theories = [];
  try { theories = (await fetch('manifest.json').then(r => r.json())).theories; } catch {}
  const files = {}, todo = [code];
  while (todo.length) {
    for (const match of todo.pop().matchAll(/^\s*load\s+([^;\n]+)/gm)) {
      for (let name of match[1].split(',').map(x => x.trim().replace(/^"|"$/g, '')).filter(Boolean)) {
        if (!name.endsWith('.kurt')) name += '.kurt';
        if (name.includes('/') || theories.includes(name) || name in files) continue;
        try { const response = await fetch(`${currentFolder}${name}`); if (response.ok) { files[name] = await response.text(); todo.push(files[name]); } } catch {}
      }
    }
  }
  return files;
}
async function runProof() {
  if (!ready || running) return;
  lastCertificate = null; $('#certificateBtn').disabled = true;
  outputPanel.classList.remove('hidden'); output.textContent = '';
  setRunning(true); setStatus('Checking proof…');
  const files = await loadedFiles(editor.value);
  worker.postMessage({ type: 'run', code: editor.value, indent: settings().indent, files });
}

// The shell under the output (the Shell button): after a run, it continues where the check stopped
// -- at its first `breakpoint`, its failing line, or after its last line -- as `kurt -i` does. A line
// typed there is checked at once; Tab completes; "Copy to editor" inserts the accepted lines there.
let shellState = null, shellEcho = '', shellStartLine = 1;
function shellStarted(state) {
  shellState = state; $('#shellBtn').disabled = !state;
  shellStartLine = state ? state.line : 1;
  if (state && state.stopped === 'breakpoint') setShell(true);       // a `breakpoint` opens it
  else if (shellOpen()) shellUpdate(state);
}
function shellOpen() { return $('#shellBtn').getAttribute('aria-pressed') === 'true'; }
function setShell(on) {
  $('#shellBtn').setAttribute('aria-pressed', String(on));
  $('#shellBar').classList.toggle('hidden', !on);
  if (on) { shellUpdate(shellState); $('#shellInput').focus(); }
  alignPanels();
}
function shellUpdate(state) {
  if (!state) return;
  shellState = state;
  const where = { breakpoint: 'at the breakpoint', error: 'at the failing line', end: 'after the last line' }[state.stopped] || '';
  $('#shellPrompt').textContent = `;[${state.line}]`;
  const next = state.next && state.next.length ? `next, e.g.: ${state.next.join('  or  ')}  (Tab writes it)` : '';
  $('#shellHint').textContent = [where && `; the shell continues ${where}`, next && `; ${next}`].filter(Boolean).join('\n');
  $('#shellInput').value = ' '.repeat(state.indent || 0);
  $('#shellCopyBtn').disabled = !(state.accepted && state.accepted.length);
}
function shellSubmit() {
  const text = $('#shellInput').value;
  if (!text.trim() || !shellState) return;
  shellEcho = `;[${shellState.line}] ${text.replace(/\n/g, '\n; ')}`;
  worker.postMessage({ type: 'shell', text });
}
function shellComplete() {
  const input = $('#shellInput'), line = input.value.slice(0, input.selectionStart);
  const word = line.match(/[^\s()\[\]{},=]*$/)[0];
  worker.postMessage({ type: 'complete', line, word });
}
function shellCompleted(items, line, word) {
  const input = $('#shellInput');
  if (input.value.slice(0, input.selectionStart) !== line) return;          // typed on meanwhile
  if (items.length === 1) {
    const before = line.slice(0, line.length - word.length), after = input.value.slice(line.length);
    input.value = before + items[0] + after;
    input.selectionStart = input.selectionEnd = (before + items[0]).length;
  } else if (items.length > 1) {
    $('#shellHint').textContent = `; ${items.slice(0, 20).join('  ')}${items.length > 20 ? '  …' : ''}`;
  }
}
function shellCopy() {
  // the accepted lines go where the shell started: before the failing line or after the breakpoint, else at the end
  const accepted = (shellState && shellState.accepted) || [];
  if (!accepted.length) return;
  const lines = editor.value.split('\n');
  const at = shellState.stopped === 'end' ? lines.length : Math.max(0, Math.min(lines.length, shellStartLine - 1));
  if (shellState.stopped === 'end' && lines.length && lines[lines.length - 1] === '') lines.pop();
  lines.splice(shellState.stopped === 'end' ? lines.length : at, 0, ...accepted);
  editor.value = lines.join('\n'); renderEditorHighlight(); persistDraft();
  setStatus(`${accepted.length} line${accepted.length > 1 ? 's' : ''} copied into the editor`);
}

function changeFontSize(step) {
  // step -1 or +1, or 0 for the default size (the View menu, and Cmd/Ctrl - / + / 0)
  updateSettings({ fontSize: step === 0 ? 15 : Math.max(10, Math.min(24, settings().fontSize + step)) });
}
function settings() {
  try { return { fontSize: 15, indent: 40, ...JSON.parse(localStorage.getItem(SETTINGS_KEY) || '{}') }; }
  catch { return { fontSize: 15, indent: 40 }; }
}
function updateSettings(patch) {
  const next = { ...settings(), ...patch };
  localStorage.setItem(SETTINGS_KEY, JSON.stringify(next));
  document.documentElement.style.setProperty('--code-font-size', `${next.fontSize}px`);
  $('#indentLabel').textContent = next.indent; $('#indentSlider').value = next.indent; $('#fontSizeLabel').textContent = next.fontSize;
  renderEditorHighlight();
}
function persistDraft() {
  clearTimeout(saveTimer);
  saveTimer = setTimeout(() => localStorage.setItem(DRAFT_KEY, JSON.stringify({ code: editor.value, filename: currentFilename, folder: currentFolder })), 250);
}
// a new file in the editor: the output (and the certificate) of the old one go
function clearOutput() {
  output.textContent = ''; outputPanel.classList.add('hidden'); lastOutputText = '';
  shellStarted(null); setShell(false);
  lastCertificate = null; $('#certificateBtn').disabled = true;
  refLines = new Set(); selfLines = new Set();
}
function setEditor(code, filename = 'proof.kurt', folder = null) {
  clearOutput();
  editor.value = code; currentFilename = filename; currentFolder = folder; renderEditorHighlight(); persistDraft();
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
  try { await navigator.clipboard.writeText(url.href); setStatus('Link to this proof copied'); }
  catch { prompt('Copy this proof link:', url.href); }
}
// what the editor shows at start: a shared link, else the last draft (you continue where you
// were), else -- on a first visit -- the first lesson of the tutorial
const FIRST_LESSON = ['proofs/tutorial/', '01-apply-an-implication-modus-ponens.kurt'];   // (00 is about the command line)
async function loadInitialDraft() {
  const shared = location.hash.match(/^#proof=(.+)$/);
  if (shared) { try { return setEditor(decodeShare(shared[1]), 'shared-proof.kurt'); } catch {} }
  try { const draft = JSON.parse(localStorage.getItem(DRAFT_KEY)); if (draft?.code) return setEditor(draft.code, draft.filename, draft.folder || null); } catch {}
  setEditor(DEFAULT_PROOF);
  try {
    const [folder, file] = FIRST_LESSON;
    const response = await fetch(`${folder}${file}`);
    if (response.ok && editor.value === DEFAULT_PROOF) setEditor(await response.text(), file, folder);
  } catch {}
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
// the lines of the proof that the reason of the hovered output line refers to (and its own)
let refLines = new Set(), selfLines = new Set();
function renderEditorHighlight() {
  const last = editor.value.split('\n').length - 1;
  editorHighlight.innerHTML = editor.value.split('\n').map((line, i) => {
    const html = highlightLine(line);
    if (refLines.has(i + 1)) return `<span class="ref-line">${html || ' '}</span>`;
    if (selfLines.has(i + 1)) return `<span class="self-line">${html || ' '}</span>`;
    return html || (i === last ? ' ' : '');     // an empty last line takes its room, as in the textarea
  }).join('\n') || '&nbsp;';
  // line numbers (the editor doesn't wrap lines, so a line of text is a row), as wide as needed
  const count = editor.value.split('\n').length;
  lineNumbers.innerHTML = Array.from({ length: count }, (_, i) => i + 1).map(n =>
    selfLines.has(n) ? `<span class="self-num">${n}</span>` : refLines.has(n) ? `<span class="ref-num">${n}</span>` : n).join('\n');
  $('#editorWrap').style.setProperty('--line-digits', String(Math.max(2, String(count).length)));
}
// the textarea is as large as its text and doesn't scroll (`.editor-wrap` does); should it ever
// scroll a little, it goes back, so that it stays on its highlighted copy
function keepEditorUnscrolled() { if (editor.scrollTop || editor.scrollLeft) { editor.scrollTop = 0; editor.scrollLeft = 0; } }
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
  linkReasons(); numberOutputLines(); alignPanels();
}
// The line numbers of the editor, on the rows of the output that echo a line: the last row with the
// number of a line in its reason (the rows before it with that number are derived, e.g. `impl-intro`
// when a block closes), and rows without a number (`proof`, `qed`) by their first word, in order.
function numberOutputLines() {
  const rows = [...output.querySelectorAll('.output-line')], source = editor.value.split('\n');
  const lines = rows.map(() => null), used = new Set(), lastRow = new Map();
  rows.forEach((row, i) => {
    const reason = reasonOf(row.textContent); if (!reason || !/^\d+$/.test(reason.id)) return;
    const owner = !row.textContent.split(';')[0].trim() && i > 0 ? i - 1 : i, line = Number(reason.id);
    if (line > source.length) return;
    if (lastRow.has(line)) lines[lastRow.get(line)] = null;
    lines[owner] = line; lastRow.set(line, owner);
  });
  lines.forEach(l => { if (l) used.add(l); });
  const firstWord = text => text.trim().split(/\s+/)[0];
  let previous = 0;
  rows.forEach((row, i) => {
    if (lines[i]) { previous = lines[i]; return; }
    const word = firstWord(row.textContent.split(';')[0]); if (!word) return;
    const next = lines.slice(i + 1).find(Boolean) || source.length + 1;
    for (let line = previous + 1; line < next; line++) {
      if (!used.has(line) && firstWord(source[line - 1]) === word) { lines[i] = line; used.add(line); previous = line; break; }
    }
  });
  rows.forEach((row, i) => { if (lines[i]) row.dataset.line = lines[i]; });
  output.style.setProperty('--line-digits', String(Math.max(2, String(Math.max(0, ...lines)).length)));
}
// Two columns: the first line of the output at the height of the first line of the editor (the
// header of the output grows by what the toolbar of the editor is higher).
function alignPanels() {
  const header = outputPanel.querySelector('.panel-header'); header.style.minHeight = '';
  if (outputPanel.classList.contains('hidden') || window.innerWidth <= 960) return;
  const gap = $('#editorWrap').getBoundingClientRect().top - output.getBoundingClientRect().top;
  if (gap > 0) header.style.minHeight = `${header.getBoundingClientRect().height + gap}px`;
}
// Each line of the output ends with its reason, e.g. `; 33 by equal-elim(33a, 32)`: its own line
// (33) and the lines its step uses (33a, 32; also ranges `21-35`, and labels of this proof, `K7`).
// The result of a block is numbered by the lines of the block, `; 21-35 by impl-intro`, and used
// by them, `by or-elim(21-35, 36-40)`.
// Hovering a line of the output marks those lines in the output and in the editor.
function reasonOf(text) {
  const found = text.match(/;\s+(\d+[a-z]?(?:-\d+[a-z]?)?)(?:\s+(.*))?$/); if (!found) return null;
  const [, id, rest = ''] = found;
  const label = rest.match(/"([^"]+)"\s*$/)?.[1] || null;
  const refs = [];
  const by = rest.match(/(?:^|\s)by\s+(.*?)(?:\s+"[^"]*")?\s*$/);
  if (by) {
    const call = by[1].match(/^([^(\s]+)(?:\((.*)\))?/);
    if (call) refs.push(call[1], ...(call[2] ? call[2].split(',').map(x => x.trim()) : []));
  }
  return { id, label, refs };
}
function linkReasons() {
  const rows = [...output.querySelectorAll('.output-line')], byId = new Map(), byLabel = new Map(), info = [];
  rows.forEach((row, i) => {
    const reason = reasonOf(row.textContent);
    // a reason on a line of its own (after a comment) belongs to the line above
    const owner = reason && !row.textContent.split(';')[0].trim() && i > 0 ? i - 1 : i;
    if (!reason) return;
    info.push({ rows: owner === i ? [row] : [rows[owner], row], ...reason });
    if (!byId.has(reason.id)) byId.set(reason.id, []);
    byId.get(reason.id).push(rows[owner], row);
    if (reason.label) byLabel.set(reason.label, reason.id);
  });
  const lineOf = id => Number(String(id).match(/^\d+/)?.[0]);
  info.forEach(item => {
    const ids = new Set(), lines = new Set(), own = item.id.includes('-');
    for (const ref of own ? [...item.refs, item.id] : item.refs) {
      const range = ref.match(/^(\d+)[a-z]?-(\d+)[a-z]?$/);
      if (range) {
        if (ref !== item.id) ids.add(ref);          // the result of that block
        for (let n = Number(range[1]); n <= Number(range[2]); n++) { ids.add(String(n)); lines.add(n); }
        continue;
      }
      const id = /^\d+[a-z]?$/.test(ref) ? ref : byLabel.get(ref);
      if (id && id !== item.id) { ids.add(id); lines.add(lineOf(id)); }
    }
    if (!ids.size) return;
    const show = on => {
      output.querySelectorAll('.output-line.ref, .output-line.self').forEach(x => x.classList.remove('ref', 'self'));
      refLines = new Set(); selfLines = new Set();
      if (on) {
        ids.forEach(id => (byId.get(id) || []).forEach(x => x.classList.add('ref')));
        item.rows.forEach(x => x.classList.add('self'));
        refLines = lines; selfLines = own ? new Set() : new Set([lineOf(item.id)]);
      }
      renderEditorHighlight();
    };
    item.rows.forEach(row => {
      row.classList.add('has-refs');
      row.title = row.title || `uses ${[...ids].map(id => `line ${id}`).join(', ')}`;
      row.addEventListener('mouseenter', () => show(true));
      row.addEventListener('mouseleave', () => show(false));
      row.addEventListener('click', () => show(!row.classList.contains('self')));     // on a phone
    });
  });
}
function goToLine(line) {
  const starts = [0]; for (let i = 0; i < editor.value.length; i++) if (editor.value[i] === '\n') starts.push(i + 1);
  const position = starts[Math.max(0, Math.min(line - 1, starts.length - 1))]; editor.focus(); editor.setSelectionRange(position, position); $('#editorWrap').scrollTop = Math.max(0, (line - 3) * parseFloat(getComputedStyle(editor).lineHeight));
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
  // the tutorial first, then the lessons on the keywords, then the course mafi1 (the examples are
  // lessons of the tutorial now)
  const order = ['tutorial/', 'keywords/', 'mafi1/'];
  const rank = folder => (order.indexOf(folder) + order.length + 1) % (order.length + 1);
  const folders = (await listDirectory('proofs/')).filter(x => x.endsWith('/')).sort((a, b) => rank(a) - rank(b) || a.localeCompare(b));
  for (const folder of folders) await createMenu(folder.slice(0, -1), `proofs/${folder}`);
  await createMenu('theories', 'theories/');
}
function toggleMenu(event, menu) {
  event.stopPropagation();
  document.querySelectorAll('.dropdown-menu').forEach(x => x !== menu && x.classList.add('hidden'));
  menu.classList.toggle('hidden');
  if (!menu.classList.contains('hidden')) {
    // fit the menu into the window below its button, so a long one scrolls instead of running off the screen
    menu.style.maxHeight = `${Math.max(160, window.innerHeight - menu.getBoundingClientRect().top - 12)}px`;
    menu.scrollTop = 0;
    // ... and inside it horizontally: on a phone, a menu opening to the left of its button
    // (`align-right`) can stick out of the screen
    menu.style.transform = '';
    const box = menu.getBoundingClientRect(), margin = 8;
    const shift = box.left < margin ? margin - box.left : Math.min(0, window.innerWidth - margin - box.right);
    if (shift) menu.style.transform = `translateX(${shift}px)`;
  }
}
async function createMenu(label, path) {
  const files = (await listDirectory(path)).filter(x => x.endsWith('.kurt')); if (!files.length) return;
  const wrapper = document.createElement('div'); wrapper.className = 'menu-wrapper';
  const button = document.createElement('button'); button.className = 'btn small'; button.textContent = label;
  const menu = document.createElement('div'); menu.className = 'dropdown-menu hidden';
  files.forEach(file => { const item = document.createElement('button'); item.className = 'item'; item.textContent = file;
    item.onclick = async () => { const response = await fetch(`${path}${file}`); if (!response.ok) return setStatus('Could not load example'); setEditor(await response.text(), file, path); menu.classList.add('hidden'); setStatus('Ready'); };
    menu.append(item);
  });
  button.onclick = event => toggleMenu(event, menu);
  wrapper.append(button, menu); examplesContainer.append(wrapper);
}

// the divider between the editor and the output (two columns only): drag it, double-click for half
// and half; the share of the editor is remembered
const SPLIT_KEY = 'kurt-playground-split';
function setSplit(share) {
  const layout = $('.layout');
  if (share === null) { layout.style.removeProperty('--left'); layout.style.removeProperty('--right'); return; }
  share = Math.min(0.85, Math.max(0.15, share));
  layout.style.setProperty('--left', `${share}fr`); layout.style.setProperty('--right', `${1 - share}fr`);
}
function setupDivider() {
  const divider = $('#divider'), layout = $('.layout');
  try { const saved = Number(localStorage.getItem(SPLIT_KEY)); if (saved) setSplit(saved); } catch {}
  divider.addEventListener('pointerdown', event => {
    event.preventDefault(); divider.setPointerCapture(event.pointerId);
    divider.classList.add('dragging'); document.body.classList.add('resizing');
  });
  divider.addEventListener('pointermove', event => {
    if (!divider.classList.contains('dragging')) return;
    const box = layout.getBoundingClientRect(), padding = 12;
    const share = (event.clientX - box.left - padding) / (box.width - 2 * padding - divider.offsetWidth);
    setSplit(share);
  });
  const stop = () => {
    if (!divider.classList.contains('dragging')) return;
    divider.classList.remove('dragging'); document.body.classList.remove('resizing');
    const left = parseFloat(layout.style.getPropertyValue('--left'));
    try { if (left) localStorage.setItem(SPLIT_KEY, String(left)); } catch {}
  };
  divider.addEventListener('pointerup', stop); divider.addEventListener('pointercancel', stop);
  divider.addEventListener('dblclick', () => { setSplit(null); try { localStorage.removeItem(SPLIT_KEY); } catch {} });
}
// the light and the dark theme (index.html sets it before the page is drawn); the button names the other
const THEME_KEY = 'kurt-playground-theme';
function setTheme(theme) {
  document.documentElement.dataset.theme = theme;
  $('#themeBtn').textContent = theme === 'light' ? 'Dark' : 'Light';
  $('meta[name="theme-color"]').setAttribute('content', theme === 'light' ? '#ffffff' : '#121521');
}
function setupTheme() {
  setTheme(document.documentElement.dataset.theme === 'light' ? 'light' : 'dark');
  $('#themeBtn').addEventListener('click', () => {
    const theme = document.documentElement.dataset.theme === 'light' ? 'dark' : 'light';
    setTheme(theme); try { localStorage.setItem(THEME_KEY, theme); } catch {}
  });
}
function setupUI() {
  setupTheme();
  setupDivider();
  window.addEventListener('resize', alignPanels);
  // (the toolbar too: while a check runs, it shows Cancel and is higher -- with the panels as high as
  // the window, the panel itself doesn't change then)
  const observer = new ResizeObserver(alignPanels);
  observer.observe($('.editor-panel')); observer.observe($('.editor-panel .toolbar'));
  loadInitialDraft(); const saved = settings(); updateSettings(saved);
  editor.addEventListener('input', () => { expandReplacement(); renderEditorHighlight(); persistDraft(); }); editor.addEventListener('scroll', keepEditorUnscrolled);
  editor.addEventListener('keydown', event => { if ((event.ctrlKey || event.metaKey) && event.key === 'Enter') { event.preventDefault(); runProof(); } });
  runBtn.onclick = runProof; cancelBtn.onclick = cancelRun; $('#shareBtn').onclick = shareProof;
  $('#copyBtn').onclick = async () => { await navigator.clipboard.writeText(lastOutputText); setStatus('Output copied'); };
  $('#clearBtn').onclick = clearOutput;
  $('#shellBtn').onclick = () => setShell(!shellOpen());
  $('#shellCopyBtn').onclick = shellCopy;
  $('#shellInput').addEventListener('keydown', event => {
    if (event.key === 'Enter' && !event.shiftKey) { event.preventDefault(); shellSubmit(); }
    else if (event.key === 'Tab') { event.preventDefault(); shellComplete(); }
  });
  $('#outputDownloadBtn').onclick = () => download('kurt-output.txt', lastOutputText);
  $('#certificateBtn').onclick = () => lastCertificate && download('proof.kurtc', lastCertificate, 'application/json');
  $('#saveBtn').onclick = () => download(currentFilename.endsWith('.kurt') ? currentFilename : `${currentFilename}.kurt`, editor.value);
  $('#loadBtn').onclick = () => { const input = document.createElement('input'); input.type = 'file'; input.accept = '.kurt,text/plain'; input.onchange = async () => input.files[0] && setEditor(await input.files[0].text(), input.files[0].name); input.click(); };
  $('#fileBtn').onclick = event => toggleMenu(event, $('#fileMenu'));
  $('#fileMenu').addEventListener('click', () => $('#fileMenu').classList.add('hidden'));   // after choosing an entry
  $('#helpBtn').onclick = () => $('#helpDialog').showModal();
  $('#helpCloseBtn').onclick = () => $('#helpDialog').close();
  $('#helpDialog').addEventListener('click', event => { if (event.target === $('#helpDialog')) $('#helpDialog').close(); });   // a click beside it
  $('#saveOutputBtn').onclick = event => toggleMenu(event, $('#saveOutputMenu'));
  $('#saveOutputMenu').addEventListener('click', event => { if (event.target.closest('.item:not(:disabled)')) $('#saveOutputMenu').classList.add('hidden'); });
  $('#viewBtn').onclick = event => toggleMenu(event, $('#viewMenu'));
  $('#fontSmallerBtn').onclick = () => changeFontSize(-1);
  $('#fontLargerBtn').onclick = () => changeFontSize(+1);
  $('#fontResetBtn').onclick = () => changeFontSize(0);
  $('#indentSlider').oninput = event => updateSettings({ indent: Number(event.target.value) });
  // a new column shows at once: check again (once the slider is let go)
  $('#indentSlider').onchange = () => { if (!outputPanel.classList.contains('hidden')) runProof(); };
  document.addEventListener('click', event => { if (!event.target.closest('.menu-wrapper')) document.querySelectorAll('.dropdown-menu').forEach(x => x.classList.add('hidden')); });
  window.addEventListener('keydown', event => { if (!(event.ctrlKey || event.metaKey)) return; if (['+','=','-','0'].includes(event.key)) { event.preventDefault(); changeFontSize(event.key === '0' ? 0 : (event.key === '-' ? -1 : 1)); } });
}

window.addEventListener('DOMContentLoaded', async () => {
  setupUI();
  try { await loadMetadata(); renderEditorHighlight(); await buildExamplesUI(); spawnWorker(); }
  catch (error) { setStatus('Initialization failed'); showOutput(error.message); }
  if ('serviceWorker' in navigator) navigator.serviceWorker.register('service-worker.js').catch(console.warn);
});
