// The editor of the playground (index.html): the proof is checked while you type (by Kurt's language server in the
// worker, as in VS Code), and the results are in the editor itself -- the reasons at the ends of the
// lines, the errors and todos underlined and in the gutter, the details of a line on hover (or in the
// bar below the editor, for phones), all problems in a list; the shell continues where a check of the
// whole proof stops, and File downloads its certificate (both from a run, as `kurt -i` and `kurt` do).
const $ = selector => document.querySelector(selector);
const editor = $('#editor');
const editorHighlight = $('#editorHighlight');
const lineNumbers = $('#lineNumbers');
const statusEl = $('#status');
const lineInfo = $('#lineInfo');
const tooltip = $('#tooltip');
const DEFAULT_PROOF = '; simple modus ponens proof\nuse A implies B\nuse A\nB\n';
const DRAFT_KEY = 'kurt.draft';          // the document in the editor
const DRAFTS_KEY = 'kurt.drafts';        // the edited files of the playground, by path: { code, original }
const SETTINGS_KEY = 'kurt.settings';
const PROBLEMS_KEY = 'kurt-next-problems-open';
const CHECK_DELAY = 400;            // ms after the last keystroke
const narrow = matchMedia('(max-width: 600px)');
let worker, ready = false, currentFilename = 'proof.kurt', currentFolder = null;
let replacements = {}, language = {}, saveTimer;

// ---- checking ---------------------------------------------------------------------------------
// The text has a version (one more with each edit); a check reports for the version it checked.
// While a check runs, an edit only notes that another check is due (`pending`).
let version = 0, checking = false, pending = false, checkTimer, cancelTimer, paused = false;
let results = null;                 // the last check: { version, diagnostics, hints, hovers, ok, todos }
let diagnosticsByLine = new Map(), hintByLine = new Map();

function setStatus(message, kind = '') { statusEl.textContent = message; statusEl.className = `status ${kind}`; }
function spawnWorker() {
  ready = false; checking = false;
  $('#checkBtn').disabled = true;
  setStatus('Loading Kurt runtime…');
  worker = new Worker('kurt-worker.js');
  worker.onmessage = async ({ data }) => {
    if (data.type === 'ready') {
      ready = true; $('#checkBtn').disabled = false;
      $('#version').textContent = `Kurt ${data.version}`;
      checkNow();
    } else if (data.type === 'progress') {
      showProgress(data);
    } else if (data.type === 'checked') {
      checked(data);
    } else if (data.type === 'editor-completions') {
      editorCompleted(data.items, data.requestId);
    } else if (data.type === 'result') {
      runFinished(data);
    } else if (data.type === 'shell-output') {
      shellOutput(data);
    } else if (data.type === 'completions') {
      shellCompleted(data.items, data.line, data.word);
    } else if (data.type === 'error') {
      checking = false; showCancel(false); hideProgress();
      setStatus('Runtime error', 'err'); showLineInfo(`Runtime error: ${data.message}`, 'err');
    }
  };
  worker.onerror = event => { setStatus('Worker failed', 'err'); showLineInfo(`Worker error: ${event.message}`, 'err'); };
}
function scheduleCheck() {
  clearTimeout(checkTimer);
  if (settings().live && !paused) checkTimer = setTimeout(checkNow, CHECK_DELAY);
}
async function checkNow() {
  clearTimeout(checkTimer);
  if (!ready) return;
  if (checking) { pending = true; return; }
  checking = true; pending = false;
  const code = editor.value, checkedVersion = version;
  setStatus('Checking…');
  clearTimeout(cancelTimer); cancelTimer = setTimeout(() => showCancel(true), 1500);
  const files = await loadedFiles(code);
  worker.postMessage({ type: 'check', code, version: checkedVersion, files });
}
// a check that takes a while: the file and line being checked (a loaded theory, the first time), and the
// files checked so far -- their number grows as `load`s are found; the bar is the part of the file done
function showProgress(data) {
  if (!checking) return;
  const line = Math.min(data.line, data.lines);
  if (matchMedia('(max-width: 600px)').matches)      // (a phone: short)
    setStatus(`${data.file} ${data.lines ? `${line}/${data.lines} ` : ''}· ${data.index}/${data.files}`);
  else setStatus(`Checking ${data.file}${data.lines ? ` · line ${line} of ${data.lines}` : ''} · file ${data.index} of ${data.files}`);
  statusEl.title = 'The files that are loaded are checked once (again only when they change); more files may follow';
  const bar = $('#progress');
  bar.classList.add('active');
  bar.firstElementChild.style.width = `${data.lines ? 100 * Math.min(data.line, data.lines) / data.lines : 0}%`;
  bar.setAttribute('aria-valuenow', String(Math.round(data.lines ? 100 * data.line / data.lines : 0)));
}
function hideProgress() { $('#progress').classList.remove('active'); statusEl.title = ''; }
function checked(data) {
  checking = false; showCancel(false); hideProgress();
  results = data;
  diagnosticsByLine = new Map(); hintByLine = new Map();
  for (const d of data.diagnostics) {
    const line = d.range.start.line;
    if (!diagnosticsByLine.has(line)) diagnosticsByLine.set(line, []);
    diagnosticsByLine.get(line).push({ severity: d.severity, message: d.message });
  }
  for (const h of data.hints) hintByLine.set(h.position.line, h.label.trim());
  // the diagnostics: an error (1), a todo (2), or a hint (4: a line that nothing later cites, Kurt 0.9)
  const errors = data.diagnostics.filter(d => d.severity === 1).length, todos = data.diagnostics.filter(d => d.severity === 2).length;
  if (errors) setStatus(`${errors} error${errors > 1 ? 's' : ''}${todos ? `, ${todos} todo${todos > 1 ? 's' : ''}` : ''}`, 'err');
  else if (todos) setStatus(`Checked, ${todos} todo${todos > 1 ? 's' : ''} left`, 'todo');
  else setStatus('Proof checked', 'ok');
  if (linkProblem) { setStatus(linkProblem, 'err'); linkProblem = null; }
  document.body.classList.toggle('stale', data.version !== version);
  renderEditor(); renderProblems(); updateLineInfo();
  if (pending || (data.version !== version && settings().live && !paused)) checkNow();
}
function showCancel(on) { $('#cancelBtn').classList.toggle('hidden', !on); clearTimeout(cancelTimer); if (!on) cancelTimer = null; }
function cancelCheck() {
  // a check that takes too long: a new runtime; no more checks while typing until the next edit
  worker.terminate(); showCancel(false); hideProgress(); paused = true; pending = false;
  spawnWorker(); setStatus('Cancelled -- edit or press Check to check again');
}
// ---- a run of the whole proof: the shell, and the certificate -----------------------------------------
// A run checks the proof as `kurt` does, up to its first error (or a `breakpoint`): the shell continues
// there, with the open blocks and the facts (`kurt -i`), and a complete proof gives the certificate
// (`.kurtc`) that the kernel checked. Started by the Shell button or File > Download certificate.
let runPurpose = null, shellState = null, shellStartLine = 1, shellVersion = -1;
async function runProof(purpose) {
  if (!ready) return;
  runPurpose = purpose;
  setStatus(purpose === 'shell' ? 'Starting the shell…' : 'Checking for the certificate…');
  const files = await loadedFiles(editor.value);
  shellVersion = version;
  worker.postMessage({ type: 'run', code: editor.value, indent: settings().indent, files });
}
function runFinished(data) {
  const purpose = runPurpose; runPurpose = null;
  if (purpose === 'certificate') {
    if (data.certificate) {
      download(`${currentFilename.replace(/\.kurt$/, '')}.kurtc`, data.certificate);
      setStatus('Certificate downloaded', 'ok');
    } else setStatus('No certificate: the proof is not checked completely', 'err');
    return;
  }
  shellState = data.shell; shellStartLine = data.shell ? data.shell.line : 1;
  $('#shellOutput').textContent = '';
  setShell(true);
  setStatus(data.exitCode ? 'Shell: the check stopped at an error' : 'Shell', data.exitCode ? 'err' : 'ok');
}
function shellOpen() { return $('#shellBtn').getAttribute('aria-pressed') === 'true'; }
function setShell(on) {
  $('#shellBtn').setAttribute('aria-pressed', String(on));
  $('#shellBar').classList.toggle('hidden', !on);
  $('#shellDivider').classList.toggle('hidden', !on);
  if (on) { shellUpdate(shellState); $('#shellInput').focus(); }
}
function shellUpdate(state) {
  if (!state) return;
  shellState = state;
  const where = { breakpoint: 'at the breakpoint', error: `at the failing line ${state.line}`, end: 'after the last line' }[state.stopped] || '';
  $('#shellPrompt').textContent = `;[${state.line}]`;
  const next = state.next && state.next.length ? `next, e.g.: ${state.next.join('  or  ')}  (Tab writes it)` : '';
  const changed = shellVersion !== version ? '; the editor has changed since: Shell again starts from its text' : '';
  $('#shellHint').textContent = [where && `; the shell continues ${where}`, next && `; ${next}`, changed].filter(Boolean).join('\n');
  $('#shellInput').value = ' '.repeat(state.indent || 0);
  $('#shellCopyBtn').disabled = !(state.accepted && state.accepted.length);
}
let shellEcho = '';
function shellSubmit() {
  const text = $('#shellInput').value;
  if (!text.trim() || !shellState) return;
  shellEcho = `;[${shellState.line}] ${text.replace(/\n/g, '\n; ')}`;
  worker.postMessage({ type: 'shell', text });
}
function shellOutput(data) {
  const out = $('#shellOutput');
  out.textContent = `${out.textContent}${out.textContent ? '\n' : ''}${shellEcho}\n${(data.output || '').trimEnd()}`.replace(/\n+$/, '');
  out.scrollTop = out.scrollHeight;
  shellUpdate(data.shell);
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
  if (shellState.stopped === 'end') {
    if (lines.length && lines[lines.length - 1] === '') lines.pop();
    lines.push(...accepted, '');
  } else lines.splice(Math.max(0, Math.min(lines.length, shellStartLine - 1)), 0, ...accepted);
  editor.value = lines.join('\n'); edited();
  setStatus(`${accepted.length} line${accepted.length > 1 ? 's' : ''} copied into the editor`);
}

// the files that `load` lines name and that are no theory, e.g. the helper of a lesson
// (`load 12-my-theory`): fetched from the folder the proof came from, also what they load -- in
// the version edited here, if there is one (as an editor uses the unsaved text of an open file)
async function loadedFiles(code) {
  if (!currentFolder) return {};
  const theories = (await getManifest()).theories || [], edited = drafts();
  // a name is relative to the file that loads it (`theory/island.kurt` may load `common` beside it),
  // and stays in the proof's folder or below it (an exercise loads its scene, `load theory/island`)
  const files = {}, todo = [{ text: code, dir: '' }];
  while (todo.length) {
    const { text, dir } = todo.pop();
    for (const match of text.matchAll(/^\s*load\s+([^;\n]+)/gm)) {
      for (let name of match[1].split(',').map(x => x.trim().replace(/^"|"$/g, '')).filter(Boolean)) {
        if (!name.endsWith('.kurt')) name += '.kurt';
        if (!name.includes('/') && theories.includes(name)) continue;
        const path = dir + name;
        if (!path.split('/').every(part => part && part !== '.' && part !== '..') || path in files) continue;
        try {
          const response = await fetch(`${currentFolder}${path}`);
          if (response.ok) {
            const text = await response.text(), draft = edited[`${currentFolder}${path}`];
            files[path] = draft ? draft.code : text;
            todo.push({ text: files[path], dir: path.slice(0, path.lastIndexOf('/') + 1) });
          }
        } catch {}
      }
    }
  }
  return files;
}

// ---- the editor: the text, highlighted, with the results ----------------------------------------
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
  return pieces.join('');
}
function colorCode(text) {
  return text.replace(grammar.declaration, m => `<span class="tok-kw1">${m}</span>`)
    .replace(grammar.command, m => `<span class="tok-kw2">${m}</span>`)
    .replace(grammar.constant, m => `<span class="tok-kw3">${m}</span>`)
    .replace(grammar.variable, m => `<span class="tok-variable">${m}</span>`)
    .replace(grammar.number, m => `<span class="tok-number">${m}</span>`);
}
function severityOf(line) {
  const list = diagnosticsByLine.get(line) || [];
  return list.some(d => d.severity === 1) ? 'err' : list.some(d => d.severity === 2) ? 'todo' : list.length ? 'unused' : '';
}
// the lines that the step of the hovered line uses (blue), and the line itself (yellow)
let refLines = new Set(), selfLines = new Set();
function renderEditor() {
  const lines = editor.value.split('\n'), { indent, reasons } = settings();
  editorHighlight.innerHTML = lines.map((line, i) => {
    let html = highlightLine(line);
    const severity = severityOf(i);
    if (severity && line.trim()) html = `<span class="diag-${severity}">${html}</span>`;       // (`diag-unused`: faded)
    const hint = reasons && hintByLine.get(i);
    if (hint) {
      // at the column of the View menu; on a narrow screen right after the text
      const pad = narrow.matches ? 2 : Math.max(2, indent - [...line].length);
      html += `<span class="hint${hint.startsWith('; qed') ? ' qed' : ''}">${' '.repeat(pad)}${escapeHtml(hint)}</span>`;
    }
    const classes = [severity && severity !== 'unused' && `${severity}-row`, refLines.has(i + 1) && 'ref-line', selfLines.has(i + 1) && 'self-line'].filter(Boolean);
    if (!html) html = i === lines.length - 1 ? ' ' : '';     // an empty last line takes its room, as in the textarea
    return classes.length ? `<span class="${classes.join(' ')}">${html || ' '}</span>` : html;
  }).join('\n') || '&nbsp;';
  lineNumbers.innerHTML = lines.map((_, i) => {
    const n = i + 1, severity = severityOf(i);
    if (selfLines.has(n)) return `<span class="self-num">${n}</span>`;
    if (refLines.has(n)) return `<span class="ref-num">${n}</span>`;
    return severity && severity !== 'unused' ? `<span class="${severity}-num">${n}</span>` : n;
  }).join('\n');
  $('#editorWrap').style.setProperty('--line-digits', String(Math.max(2, String(lines.length).length)));
}
function keepEditorUnscrolled() { if (editor.scrollTop || editor.scrollLeft) { editor.scrollTop = 0; editor.scrollLeft = 0; } }

// ---- what Kurt says about a line --------------------------------------------------------------
// The reason of a line, e.g. `; by 3(4)`, or `; 9a by ...` for a derived line: the lines its step uses
// (3, 4; also ranges `21-35`, and labels of this proof).
function reasonOf(text, line) {
  const found = text.match(/;\s+(?:qed\s+)?(?:(\d+[a-z]?(?:-\d+[a-z]?)?)(?:\s+|$))?(.*)$/); if (!found) return null;
  const id = found[1] || String(line), rest = found[2] || '';
  const refs = [];
  const by = rest.match(/(?:^|\s)by\s+(.*?)(?:\s+"[^"]*")?\s*$/);
  if (by) {
    const call = by[1].match(/^([^(\s]+)(?:\((.*)\))?/);
    if (call) refs.push(call[1], ...(call[2] ? call[2].split(',').map(x => x.trim()) : []));
  }
  return { id, refs };
}
function usedLines(line) {
  // (0-based line) -> the 1-based lines its step uses
  const hint = hintByLine.get(line); if (!hint) return new Set();
  const reason = reasonOf(hint, line + 1); if (!reason) return new Set();
  const labels = new Map();
  for (const [n, h] of hintByLine) { const label = h.match(/"([^"]+)"\s*$/)?.[1]; if (label) labels.set(label, n + 1); }
  const lines = new Set(), own = reason.id.includes('-');
  for (const ref of own ? [...reason.refs, reason.id] : reason.refs) {
    const range = ref.match(/^(\d+)[a-z]?-(\d+)[a-z]?$/);
    if (range) { for (let n = Number(range[1]); n <= Number(range[2]); n++) lines.add(n); continue; }
    const number = ref.match(/^(\d+)[a-z]?$/)?.[1];
    if (number) lines.add(Number(number)); else if (labels.has(ref)) lines.add(labels.get(ref));
  }
  lines.delete(line + 1);
  return lines;
}
function markLine(line) {
  // (0-based line, or null) marks it and the lines its step uses
  const next = line === null ? new Set() : usedLines(line);
  const self = line === null || !next.size ? new Set() : new Set([line + 1]);
  if ([...next].join() === [...refLines].join() && [...self].join() === [...selfLines].join()) return;
  refLines = next; selfLines = self; renderEditor();
}
// the hover of the language server is Markdown: a code block (the line and its reason), then
// `**name:** text` lines, with `code` and links to lines (`[line 3](file:///play/proof.kurt#L3)`),
// to a loaded file (`[island.kurt:12](file:///play/theory/island.kurt#L12)`, in /play: the proof's
// folder) and to the theories that come with Kurt (`propositional.kurt:75`, `**theory:** \`propositional\``: no
// path, they are inside kurt.py) -- a link to another file opens it (`#file=...&line=...`)
function fileLink(path, line, text) {
  return `<a href="#file=${path}${line ? `&line=${line}` : ''}">${text}</a>`;
}
function markdownToHtml(markdown) {
  const theories = (manifestCache && manifestCache.theories) || [], theory = name => theories.includes(name);
  const parts = markdown.split(/```kurt\n([\s\S]*?)\n```/);
  return parts.map((part, i) => {
    if (i % 2) return `<pre>${part.split('\n').map(highlightLine).join('\n')}</pre>`;
    if (!part.trim()) return '';
    let html = escapeHtml(part.trim());
    const links = [];
    html = html.replace(/\[([^\]]+)\]\(([^)\s]+)\)/g, (_, text, url) => {
      const found = url.match(/^file:\/\/\/play\/([^#]+?)(?:#L(\d+))?$/);
      if (!found) return text;
      const [, path, line] = found;
      links.push(path === 'proof.kurt' ? (line ? `<a href="#" data-line="${line}">${text}</a>` : text)
        : fileLink(`${currentFolder || ''}${path}`, line, text));
      return `\u0000${links.length - 1}\u0000`;
    });
    html = html.replace(/(?<![\w/.-])([\w-]+\.kurt):(\d+)\b/g, (all, name, line) => theory(name) ? fileLink(`theories/${name}`, line, all) : all);
    html = html.replace(/\*\*theory:\*\*[^\n]*/, line => line.replace(/`([\w-]+)`/g, (all, name) => theory(`${name}.kurt`) ? fileLink(`theories/${name}.kurt`, '', all) : all));
    html = html.replace(/\u0000(\d+)\u0000/g, (_, n) => links[Number(n)]);
    html = html.replace(/\*\*([^*]+)\*\*/g, '<strong>$1</strong>').replace(/`([^`]+)`/g, '<code>$1</code>');
    return `<p>${html.replace(/ {2}\n/g, '<br>').replace(/\n\n/g, '</p><p>').replace(/\n/g, '<br>')}</p>`;
  }).join('');
}
function lineDetailsHtml(line) {
  // (0-based) the errors and todos of a line, then how it follows
  const diagnostics = (diagnosticsByLine.get(line) || []).map(d =>
    `<div class="diag ${d.severity === 1 ? 'err' : d.severity === 2 ? 'todo' : 'hint'}">${escapeHtml(d.message)}</div>`).join('');
  const hover = results && results.hovers[line];
  return diagnostics + (hover ? markdownToHtml(hover) : '');
}
function lineSummary(line) {
  // (0-based) one line about a line, for the bar below the editor
  const diagnostic = (diagnosticsByLine.get(line) || []).find(d => d.severity !== 4);
  if (diagnostic) return { text: `${line + 1}: ${diagnostic.message.split('\n')[0]}`, kind: diagnostic.severity === 1 ? 'err' : 'todo' };
  const hint = hintByLine.get(line);
  if (hint) return { text: `${line + 1}: ${editor.value.split('\n')[line].trim()}   ${hint}`, kind: '' };
  return null;
}

// the bar below the editor: what Kurt says about the line of the cursor (tap: the details), or a hint of Tab
let infoLine = null, completionHint = '';
function caretLine() { return editor.value.slice(0, editor.selectionStart).split('\n').length - 1; }
function showLineInfo(text, kind = '') {
  lineInfo.classList.remove('open'); lineInfo.className = `line-info ${kind}`;
  lineInfo.textContent = text;
}
function updateLineInfo() {
  if (completionHint) return showLineInfo(completionHint);
  infoLine = caretLine();
  const summary = lineSummary(infoLine);
  showLineInfo(summary ? summary.text : '', summary ? summary.kind : '');
}
function toggleLineDetails() {
  if (infoLine === null || completionHint) return;
  if (lineInfo.classList.contains('open')) return updateLineInfo();
  const html = lineDetailsHtml(infoLine);
  if (!html) return;
  lineInfo.innerHTML = html; lineInfo.classList.add('open');
}

// the details on hover (with a mouse): over a line for a moment
let hoverLine = null, hoverTimer, hideTimer;
function lineAt(clientY) {
  const box = editor.getBoundingClientRect(), style = getComputedStyle(editor);
  const line = Math.floor((clientY - box.top - parseFloat(style.paddingTop)) / parseFloat(style.lineHeight));
  return line >= 0 && line < editor.value.split('\n').length ? line : null;
}
function editorHover(event) {
  const line = lineAt(event.clientY);
  if (line === hoverLine) return;
  hoverLine = line; clearTimeout(hoverTimer); hideTooltip();
  markLine(line);
  if (line === null || !settings().hover) return;       // (View: "Details when hovering a line")
  hoverTimer = setTimeout(() => showTooltip(line, event.clientX), 350);
}
function showTooltip(line, x) {
  const html = lineDetailsHtml(line);
  if (!html) return;
  clearTimeout(hideTimer);
  tooltip.innerHTML = html; tooltip.classList.remove('hidden');
  const box = editor.getBoundingClientRect(), style = getComputedStyle(editor);
  const lineHeight = parseFloat(style.lineHeight), top = box.top + parseFloat(style.paddingTop) + (line + 1) * lineHeight + 4;
  const width = tooltip.offsetWidth, height = tooltip.offsetHeight;
  tooltip.style.left = `${Math.max(8, Math.min(x - 24, window.innerWidth - width - 8))}px`;
  // below the line, or above it where there is no room below
  tooltip.style.top = `${top + height < window.innerHeight - 8 ? top : Math.max(8, top - lineHeight - height - 8)}px`;
}
function hideTooltip() { tooltip.classList.add('hidden'); }
function leaveEditor() {
  clearTimeout(hoverTimer); hoverLine = null;
  hideTimer = setTimeout(() => { hideTooltip(); markLine(null); }, 250);
}

// all errors and todos, below the editor
function renderProblems() {
  const list = $('#problemsList'), summary = $('#problemsSummary');
  const every = [...diagnosticsByLine.entries()].sort((a, b) => a[0] - b[0]).flatMap(([line, ds]) => ds.map(d => ({ line, ...d })));
  const all = every.filter(d => d.severity !== 4), unused = every.length - all.length;      // (the hints: in the details only)
  const errors = all.filter(d => d.severity === 1).length, todos = all.length - errors;
  const hint = unused ? ` <span class="count-hint">(${unused} line${unused > 1 ? 's' : ''} not used)</span>` : '';
  summary.innerHTML = !results ? 'Problems' : all.length
    ? `Problems: ${[errors && `<span class="count-err">${errors} error${errors > 1 ? 's' : ''}</span>`, todos && `<span class="count-todo">${todos} todo${todos > 1 ? 's' : ''}</span>`].filter(Boolean).join(', ')}${hint}`
    : `<span class="count-ok">No problems</span>: every line is checked${hint}`;
  list.innerHTML = '';
  for (const d of all) {
    const row = document.createElement('button'); row.type = 'button';
    row.className = `problem ${d.severity === 1 ? 'err' : 'todo'}`;
    row.innerHTML = `<span class="where">line ${d.line + 1}</span><span class="what">${escapeHtml(d.message)}</span>`;
    row.onclick = () => goToLine(d.line + 1);
    list.append(row);
  }
}
function goToLine(line) {
  const starts = [0]; for (let i = 0; i < editor.value.length; i++) if (editor.value[i] === '\n') starts.push(i + 1);
  const position = starts[Math.max(0, Math.min(line - 1, starts.length - 1))];
  editor.focus({ preventScroll: true }); editor.setSelectionRange(position, position);
  const wrap = $('#editorWrap'), lineHeight = parseFloat(getComputedStyle(editor).lineHeight);
  const y = (line - 1) * lineHeight;
  if (y < wrap.scrollTop || y > wrap.scrollTop + wrap.clientHeight - 3 * lineHeight) wrap.scrollTop = Math.max(0, y - 3 * lineHeight);
  wrap.scrollLeft = 0;
  updateLineInfo();
}

// ---- Tab completion (the state at the cursor; the worker's `editor-complete`) --------------------
let completionTimer, completionId = 0, completionPending = null;
function editorContext() {
  const position = editor.selectionStart, before = editor.value.slice(0, position);
  const start = before.lastIndexOf('\n') + 1, line = before.slice(start);
  return { position, before, prefix: before.slice(0, start), line, word: line.match(/[^\s()\[\]{},=]*$/)[0] };
}
function usefulHint({ line }) {
  const stripped = line.trim();
  return !stripped || stripped.endsWith('=') || /\\[A-Za-z]*$/.test(line) || /^\s*load(?:\s+\S*)?$/.test(line);
}
async function requestCompletion(mode) {
  if (!ready) return;
  const context = editorContext();
  if (mode === 'hint' && !usefulHint(context)) return;
  const requestId = ++completionId;
  completionPending = { ...context, mode, requestId };
  const files = await loadedFiles(editor.value);
  if (!completionPending || completionPending.requestId !== requestId || editor.selectionStart !== context.position) return;
  worker.postMessage({ type: 'editor-complete', prefix: context.prefix, line: context.line, word: context.word, files, requestId });
}
function scheduleCompletionHint() {
  clearTimeout(completionTimer); completionPending = null; completionHint = '';
  updateLineInfo();
  if (usefulHint(editorContext())) completionTimer = setTimeout(() => requestCompletion('hint'), 250);
}
function editorCompleted(items, requestId) {
  const pending = completionPending;
  if (!pending || pending.requestId !== requestId || editor.selectionStart !== pending.position ||
      editor.value.slice(0, pending.position) !== pending.before) return;
  const shown = items.slice(0, 8).join('  or  ');
  completionHint = shown ? `Tab: ${shown}${items.length > 8 ? '  …' : ''}` : '';
  updateLineInfo();
  if (pending.mode !== 'tab' || items.length !== 1) return;
  editor.setRangeText(items[0], pending.position - pending.word.length, pending.position, 'end');
  edited();
}

// ---- editing ----------------------------------------------------------------------------------
function edited() {
  version++; document.body.classList.add('stale'); paused = false;
  renderEditor(); persistDraft(); scheduleCompletionHint(); scheduleCheck();
}
function expandReplacement() {
  const caret = editor.selectionStart, trigger = editor.value[caret - 1];
  if (!trigger || /[A-Za-z0-9]/.test(trigger)) return;
  const match = editor.value.slice(0, caret - 1).match(/(\\[A-Za-z]+)$/);
  if (!match || !replacements[match[1]]) return;
  const start = caret - 1 - match[1].length, trailing = trigger === '\n' ? '\n' : (trigger === ' ' ? '' : trigger);
  editor.value = editor.value.slice(0, start) + replacements[match[1]] + trailing + editor.value.slice(caret);
  const next = start + replacements[match[1]].length + trailing.length;
  editor.setSelectionRange(next, next);
}
function newlineKeepingIndent() {
  // Enter: the new line starts as indented as this one (blocks are indented)
  const { line } = editorContext();
  editor.setRangeText('\n' + line.match(/^ */)[0], editor.selectionStart, editor.selectionEnd, 'end');
  edited();
}
function insertAtCursor(text) {
  editor.setRangeText(text, editor.selectionStart, editor.selectionEnd, 'end'); editor.focus(); edited();
}
function persistDraft() {
  clearTimeout(saveTimer);
  saveTimer = setTimeout(() => {
    try { localStorage.setItem(DRAFT_KEY, JSON.stringify({ code: editor.value, filename: currentFilename, folder: currentFolder, original: currentOriginal })); } catch {}
    // a file of the playground: its edited version stays, by its path (and is used when another file loads it)
    const path = currentPath();
    if (path) {
      const all = drafts();
      if (editor.value === currentOriginal) delete all[path]; else all[path] = { code: editor.value, original: currentOriginal };
      saveDrafts(all);
    }
    updateFileMenu();
  }, 250);
}
function drafts() { try { return JSON.parse(localStorage.getItem(DRAFTS_KEY)) || {}; } catch { return {}; } }
function saveDrafts(all) { try { localStorage.setItem(DRAFTS_KEY, JSON.stringify(all)); } catch {} }
function currentPath() { return currentFolder !== null && currentOriginal !== null ? `${currentFolder}${currentFilename}` : null; }
function updateFileMenu() {
  const changed = currentOriginal !== null && editor.value !== currentOriginal;
  $('#revertBtn').classList.toggle('hidden', !changed);
  $('#revertBtn').textContent = `Discard my changes to ${currentFilename}`;
}
function revertFile() {
  // the file as it came: the edited version is dropped
  if (currentOriginal === null) return;
  const all = drafts(); delete all[currentPath()]; saveDrafts(all);
  const original = currentOriginal;
  setEditor(original, currentFilename, currentFolder); currentOriginal = original; persistDraft();
}
function setEditor(code, filename = 'proof.kurt', folder = null) {
  setShell(false); shellState = null;               // (the shell of another file)
  editor.value = code; currentFilename = filename; currentFolder = folder; currentOriginal = null;
  results = null; diagnosticsByLine = new Map(); hintByLine = new Map(); refLines = new Set(); selfLines = new Set();
  renderProblems(); $('#editorWrap').scrollTop = 0;
  edited(); checkNow();
}

// ---- settings, files, menus ---------------------------------------------------------------------
function settings() {
  const defaults = { fontSize: 15, indent: 40, live: true, reasons: true, hover: true, shellSide: false, shellSize: 0, shellWidth: 0 };
  try { return { ...defaults, ...JSON.parse(localStorage.getItem(SETTINGS_KEY) || '{}') }; } catch { return defaults; }
}
function updateSettings(patch) {
  const next = { ...settings(), ...patch };
  try { localStorage.setItem(SETTINGS_KEY, JSON.stringify(next)); } catch {}
  document.documentElement.style.setProperty('--code-font-size', `${next.fontSize}px`);
  $('#indentLabel').textContent = next.indent; $('#indentSlider').value = next.indent; $('#fontSizeLabel').textContent = next.fontSize;
  $('#liveToggle').checked = next.live; $('#reasonsToggle').checked = next.reasons; $('#hoverToggle').checked = next.hover; $('#shellSideToggle').checked = next.shellSide;
  applyShellLayout(next);
  renderEditor();
}
// the shell below the editor or beside it (View), and the size the divider gave it (0: the default)
function applyShellLayout(s = settings()) {
  document.body.classList.toggle('shell-side', !!s.shellSide);
  const layout = $('.next-layout');
  if (s.shellSize) layout.style.setProperty('--shell-size', `${s.shellSize}px`); else layout.style.removeProperty('--shell-size');
  if (s.shellWidth) layout.style.setProperty('--shell-width', `${s.shellWidth}px`); else layout.style.removeProperty('--shell-width');
}
function shellBeside() { return settings().shellSide && matchMedia('(min-width: 961px)').matches; }
function startShellResize(event) {
  // drag the divider: up and down, or (the shell beside the editor) left and right
  event.preventDefault();
  const divider = $('#shellDivider'), side = shellBeside(), box = $('.next-layout').getBoundingClientRect();
  divider.classList.add('dragging'); document.body.classList.add(side ? 'resizing' : 'resizing-rows');
  const move = e => {
    if (side) updateSettings({ shellWidth: Math.round(Math.max(220, Math.min(box.right - 12 - e.clientX, box.width - 320))) });
    else updateSettings({ shellSize: Math.round(Math.max(90, Math.min(box.bottom - 12 - e.clientY, box.height - 220))) });
  };
  const up = () => {
    window.removeEventListener('pointermove', move);
    divider.classList.remove('dragging'); document.body.classList.remove('resizing', 'resizing-rows');
  };
  window.addEventListener('pointermove', move);
  window.addEventListener('pointerup', up, { once: true });
}
function changeFontSize(step) { updateSettings({ fontSize: step === 0 ? 15 : Math.max(10, Math.min(24, settings().fontSize + step)) }); }
function encodeShare(text) {
  const bytes = new TextEncoder().encode(text);
  let binary = ''; bytes.forEach(byte => { binary += String.fromCharCode(byte); });
  return btoa(binary).replace(/\+/g, '-').replace(/\//g, '_').replace(/=+$/, '');
}
function decodeShare(value) {
  const binary = atob(value.replace(/-/g, '+').replace(/_/g, '/'));
  return new TextDecoder().decode(Uint8Array.from(binary, c => c.charCodeAt(0)));
}
// A file of the playground is opened from its folder (so its `load`s find their files) and in the
// version edited here, if there is one (`drafts`); the address bar shows it
// (`#file=exercises/01-knights-and-knaves/2-two-islanders.kurt`, with `&line=12` from a link in the
// details), and the browser's Back button returns to the file before -- only a file that the
// manifest lists, so a link can't fetch anything else. Share gives such a link while the file is
// unchanged; an edited one goes as the text, with its folder (`#proof=...&folder=...`)
let currentOriginal = null;      // the text of the playground file in the editor, as it was opened
let linkProblem = null;          // a link to no file: said once the runtime is there (instead of its first status)
let manifestCache = null;
async function getManifest() {
  if (!manifestCache) { try { manifestCache = await fetch('manifest.json').then(r => r.json()); } catch { return {}; } }
  return manifestCache;
}
async function manifestFiles(folder) {
  const manifest = await getManifest();
  if (folder === 'theories/') return manifest.theories || [];
  const topic = folder.match(/^exercises\/([^/]+)\/$/)?.[1], scene = folder.match(/^exercises\/([^/]+)\/theory\/$/)?.[1];
  return (topic ? manifest.exercises?.[topic] : scene ? manifest.scenes?.[scene] : manifest.folders?.[folder]) || [];
}
function fileHash(path, line) { return `#file=${path}${line ? `&line=${line}` : ''}`; }
// `how`: 'push' (a menu, a link in the details: the document left behind becomes a history entry,
// so Back returns to it), 'replace' (the start), 'here' (the address bar names the file already:
// a pasted link, Back)
async function showPlaygroundFile(folder, file, line = 0, how = 'push') {
  try {
    const response = await fetch(`${folder}${file}`); if (!response.ok) return false;
    const text = await response.text(), path = `${folder}${file}`, draft = drafts()[path];
    if (how === 'push') {
      // the document left behind: a file by its name (its edits stay by its path), anything else by its text
      if (currentPath()) history.replaceState(null, '', fileHash(currentPath()));
      else if (editor.value.trim() && editor.value !== DEFAULT_PROOF) {
        history.replaceState(null, '', `#proof=${encodeShare(editor.value)}${currentFolder ? `&folder=${currentFolder}` : ''}`);
      }
      history.pushState(null, '', fileHash(path, line));
    } else if (how === 'replace') history.replaceState(null, '', fileHash(path, line));
    setEditor(draft && draft.code !== text ? draft.code : text, file, folder); currentOriginal = text; persistDraft();
    if (line) goToLine(line);
    return true;
  } catch { return false; }
}
async function openPath(path, line, how) {
  // a file by its path, only one that the manifest lists
  const at = path.lastIndexOf('/') + 1, [folder, file] = [path.slice(0, at), path.slice(at)];
  if ((await manifestFiles(folder)).includes(file) && await showPlaygroundFile(folder, file, line, how)) return true;
  const problem = `The playground has no file ${path}`; if (!ready) linkProblem = problem; setStatus(problem, 'err'); return false;
}
async function openFromLink() {
  const link = new URLSearchParams(location.hash.slice(1));
  if (link.has('file')) return openPath(link.get('file'), Number(link.get('line')) || 0, 'here');
  if (link.has('proof')) {
    try {
      const code = decodeShare(link.get('proof')), folder = link.get('folder');
      const known = folder && (await manifestFiles(folder)).length > 0;
      setEditor(code, 'shared-proof.kurt', known ? folder : null); return true;
    } catch {}
  }
  return false;
}
async function shareProof() {
  const url = new URL(location.href);
  const unchanged = currentOriginal !== null && editor.value === currentOriginal;
  url.hash = unchanged ? `file=${currentFolder}${currentFilename}`
    : `proof=${encodeShare(editor.value)}` + (currentFolder ? `&folder=${currentFolder}` : '');
  history.replaceState(null, '', url);          // (the link in the address bar too)
  const what = unchanged ? 'file' : 'proof';
  const note = unchanged ? '' : currentOriginal !== null ? ' (it carries your text: the file is changed)' : ' (it carries the text)';
  try { await navigator.clipboard.writeText(url.href); setStatus(`Link to this ${what} copied${note}`); }
  catch { prompt(`Copy this ${what} link:`, url.href); }
}
const FIRST_LESSON = ['tutorial/', '01-apply-an-implication-modus-ponens.kurt'];
async function loadInitialDraft() {
  if (await openFromLink()) return;
  try {
    const draft = JSON.parse(localStorage.getItem(DRAFT_KEY));
    if (draft?.code) {
      // a file of the playground: opened again (its edited version is kept by its path); else the text
      if (draft.folder && draft.original != null && draft.filename && await showPlaygroundFile(draft.folder, draft.filename, 0, 'replace')) return;
      setEditor(draft.code, draft.filename, draft.folder || null); currentOriginal = draft.original ?? null; return;
    }
  } catch {}
  setEditor(DEFAULT_PROOF);
  try {
    const [folder, file] = FIRST_LESSON;
    if (editor.value === DEFAULT_PROOF) await showPlaygroundFile(folder, file, 0, 'replace');
  } catch {}
}
function download(name, text, type = 'text/plain;charset=utf-8') {
  const link = document.createElement('a');
  link.href = URL.createObjectURL(new Blob([text], { type })); link.download = name; link.click();
  setTimeout(() => URL.revokeObjectURL(link.href), 0);
}
async function loadMetadata() {
  [replacements, language] = await Promise.all([
    fetch('replacements.json').then(r => r.json()), fetch('language.json').then(r => r.json()), getManifest()
  ]);
  buildGrammar(); buildSymbolBar();
}
function buildSymbolBar() {
  const bar = $('#symbolBar'); bar.innerHTML = '';
  ['∀','∃','⇒','⇔','¬','∧','∨','⊥','∈','∉','⊆','∪','∩','≤','≥','≠','∞'].forEach(symbol => {
    const button = document.createElement('button'); button.className = 'symbol'; button.textContent = symbol; button.type = 'button';
    button.onmousedown = event => event.preventDefault();       // the editor keeps its cursor
    button.onclick = () => insertAtCursor(symbol); bar.append(button);
  });
}
async function listDirectory(path) {
  try { const data = await fetch(`/__list?path=${encodeURIComponent(path)}`).then(r => r.json()); const entries = [...data.dirs, ...data.files]; if (entries.length) return entries; } catch {}
  return manifestFiles(path);
}
// the menus of the proofs: the folders of the manifest, as in Kurt's repository (`tutorial/`,
// `keywords/`, `proofs/mafi1/`), named by their last part -- so a link to a file is readable,
// `#file=tutorial/02-prove-an-implication.kurt`
async function buildExamplesUI() {
  const folders = Object.keys((await getManifest()).folders || {});
  for (const folder of folders) await createMenu(folder.slice(0, -1).split('/').pop(), folder);
  await createExercisesMenu();
  await createMenu('theories', 'theories/');
}
// the exercises, by topic: each loads its scene from the folder `theory/` beside it
async function createExercisesMenu() {
  const topics = (await getManifest()).exercises || {};
  if (!Object.keys(topics).length) return;
  const wrapper = document.createElement('div'); wrapper.className = 'menu-wrapper';
  const button = document.createElement('button'); button.className = 'btn small'; button.textContent = 'exercises';
  const menu = document.createElement('div'); menu.className = 'dropdown-menu hidden';
  for (const [topic, files] of Object.entries(topics)) {
    const heading = document.createElement('div'); heading.className = 'menu-heading';
    heading.textContent = topic.replace(/^\d+-/, '').replaceAll('-', ' ');
    menu.append(heading);
    const path = `exercises/${topic}/`;
    files.forEach(file => {
      const item = document.createElement('button'); item.className = 'item'; item.textContent = file;
      item.onclick = async () => { if (!await showPlaygroundFile(path, file)) return setStatus('Could not load the exercise', 'err'); menu.classList.add('hidden'); };
      menu.append(item);
    });
  }
  button.onclick = event => toggleMenu(event, menu);
  wrapper.append(button, menu); $('#examplesContainer').append(wrapper);
}
function toggleMenu(event, menu) {
  event.stopPropagation();
  document.querySelectorAll('.dropdown-menu').forEach(x => x !== menu && x.classList.add('hidden'));
  menu.classList.toggle('hidden');
  if (!menu.classList.contains('hidden')) {
    const panel = menu.closest('.panel');
    const bottom = Math.min(window.innerHeight, panel ? panel.getBoundingClientRect().bottom : Infinity);
    menu.style.maxHeight = `${Math.max(160, bottom - menu.getBoundingClientRect().top - 12)}px`;
    menu.scrollTop = 0; menu.style.transform = '';
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
  files.forEach(file => {
    const item = document.createElement('button'); item.className = 'item'; item.textContent = file;
    item.onclick = async () => { if (!await showPlaygroundFile(path, file)) return setStatus('Could not load example', 'err'); menu.classList.add('hidden'); };
    menu.append(item);
  });
  button.onclick = event => toggleMenu(event, menu);
  wrapper.append(button, menu); $('#examplesContainer').append(wrapper);
}
const THEME_KEY = 'kurt-playground-theme';
function setTheme(theme) {
  document.documentElement.dataset.theme = theme;
  $('#themeBtn').textContent = theme === 'light' ? 'Dark' : 'Light';
  $('meta[name="theme-color"]').setAttribute('content', theme === 'light' ? '#ffffff' : '#121521');
}

function setupUI() {
  setTheme(document.documentElement.dataset.theme === 'light' ? 'light' : 'dark');
  $('#themeBtn').onclick = () => {
    const theme = document.documentElement.dataset.theme === 'light' ? 'dark' : 'light';
    setTheme(theme); try { localStorage.setItem(THEME_KEY, theme); } catch {}
  };
  updateSettings({});
  narrow.addEventListener('change', renderEditor);
  editor.addEventListener('input', event => { if (event.inputType !== 'insertLineBreak') expandReplacement(); edited(); });
  editor.addEventListener('scroll', keepEditorUnscrolled);
  editor.addEventListener('keydown', event => {
    if ((event.ctrlKey || event.metaKey) && event.key === 'Enter') { event.preventDefault(); paused = false; checkNow(); }
    else if (event.key === 'Tab' && !event.shiftKey) { event.preventDefault(); requestCompletion('tab'); }
    else if (event.key === 'Enter' && !event.shiftKey && !event.altKey && !event.isComposing) {
      event.preventDefault(); expandReplacement(); newlineKeepingIndent();
    }
  });
  document.addEventListener('selectionchange', () => { if (document.activeElement === editor && !completionHint) updateLineInfo(); });
  editor.addEventListener('click', scheduleCompletionHint);
  // hover (a mouse); on a touch screen, the bar below the editor
  editor.addEventListener('mousemove', editorHover);
  editor.addEventListener('mouseleave', leaveEditor);
  tooltip.addEventListener('mouseenter', () => clearTimeout(hideTimer));
  tooltip.addEventListener('mouseleave', leaveEditor);
  const followLink = event => {
    // a line of this file, or another file (`#file=...&line=...`: opened as from a menu, Back returns)
    const link = event.target.closest('a[href]'); if (!link) return;
    event.preventDefault(); hideTooltip();
    if (link.dataset.line) return goToLine(Number(link.dataset.line));
    const target = new URLSearchParams(link.getAttribute('href').slice(1));
    if (target.has('file')) void openPath(target.get('file'), Number(target.get('line')) || 0, 'push');
  };
  tooltip.addEventListener('click', followLink);
  lineInfo.addEventListener('click', event => { if (event.target.closest('a[href]')) return followLink(event); toggleLineDetails(); });
  $('#editorWrap').addEventListener('scroll', hideTooltip);
  $('#checkBtn').onclick = () => { paused = false; checkNow(); };
  $('#shellBtn').onclick = () => shellOpen() ? setShell(false) : runProof('shell');
  $('#certificateBtn').onclick = () => runProof('certificate');
  $('#shellCloseBtn').onclick = () => setShell(false);
  $('#shellDivider').addEventListener('pointerdown', startShellResize);
  $('#shellDivider').addEventListener('dblclick', () => updateSettings(shellBeside() ? { shellWidth: 0 } : { shellSize: 0 }));
  $('#shellSideToggle').onchange = event => updateSettings({ shellSide: event.target.checked });
  $('#shellCopyBtn').onclick = shellCopy;
  $('#shellInput').addEventListener('keydown', event => {
    if (event.key === 'Enter' && !event.shiftKey && !event.isComposing) { event.preventDefault(); shellSubmit(); }
    else if (event.key === 'Tab' && !event.shiftKey) { event.preventDefault(); shellComplete(); }
  });
  $('#cancelBtn').onclick = cancelCheck;
  $('#shareBtn').onclick = shareProof;
  $('#saveBtn').onclick = () => download(currentFilename.endsWith('.kurt') ? currentFilename : `${currentFilename}.kurt`, editor.value);
  $('#loadBtn').onclick = () => {
    const input = document.createElement('input'); input.type = 'file'; input.accept = '.kurt,text/plain';
    input.onchange = async () => {
      if (!input.files[0]) return;
      history.pushState(null, '', location.pathname + location.search);       // (no longer the file of the address bar)
      setEditor(await input.files[0].text(), input.files[0].name);
    };
    input.click();
  };
  $('#revertBtn').onclick = revertFile;
  $('#fileBtn').onclick = event => toggleMenu(event, $('#fileMenu'));
  $('#fileMenu').addEventListener('click', () => $('#fileMenu').classList.add('hidden'));
  $('#viewBtn').onclick = event => toggleMenu(event, $('#viewMenu'));
  $('#viewMenu').addEventListener('click', event => event.stopPropagation());
  $('#fontSmallerBtn').onclick = () => changeFontSize(-1);
  $('#fontLargerBtn').onclick = () => changeFontSize(+1);
  $('#fontResetBtn').onclick = () => changeFontSize(0);
  $('#indentSlider').oninput = event => updateSettings({ indent: Number(event.target.value) });
  $('#liveToggle').onchange = event => { updateSettings({ live: event.target.checked }); if (event.target.checked) checkNow(); };
  $('#reasonsToggle').onchange = event => updateSettings({ reasons: event.target.checked });
  $('#hoverToggle').onchange = event => { updateSettings({ hover: event.target.checked }); if (!event.target.checked) hideTooltip(); };   // (the details stay in the problems list)
  $('#helpBtn').onclick = () => $('#helpDialog').showModal();
  $('#helpCloseBtn').onclick = () => $('#helpDialog').close();
  $('#helpDialog').addEventListener('click', event => { if (event.target === $('#helpDialog')) $('#helpDialog').close(); });
  try { $('#problems').open = localStorage.getItem(PROBLEMS_KEY) === 'true'; } catch {}
  $('#problems').addEventListener('toggle', () => { try { localStorage.setItem(PROBLEMS_KEY, String($('#problems').open)); } catch {} });
  document.addEventListener('click', event => { if (!event.target.closest('.menu-wrapper')) document.querySelectorAll('.dropdown-menu').forEach(x => x.classList.add('hidden')); });
  window.addEventListener('keydown', event => {
    if (!(event.ctrlKey || event.metaKey)) return;
    if (['+', '=', '-', '0'].includes(event.key)) { event.preventDefault(); changeFontSize(event.key === '0' ? 0 : (event.key === '-' ? -1 : 1)); }
  });
}

window.addEventListener('DOMContentLoaded', async () => {
  setupUI();
  try { await loadMetadata(); await loadInitialDraft(); await buildExamplesUI(); spawnWorker(); }
  catch (error) { setStatus('Initialization failed', 'err'); showLineInfo(error.message, 'err'); }
  window.addEventListener('hashchange', openFromLink);      // a link pasted into this tab
  if ('serviceWorker' in navigator) navigator.serviceWorker.register('service-worker.js').catch(console.warn);
});
