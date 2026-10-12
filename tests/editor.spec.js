const { test, expect } = require('@playwright/test');

// the editor (index.html): checked while typing, the results in the editor

test.beforeEach(async ({ page }) => {
  await page.goto('/');
  await expect(page.locator('#version')).toHaveText(/^Kurt \d/, { timeout: 60000 });
});

async function typeProof(page, text) {
  await page.locator('#editor').fill(text);
  await expect(page.locator('body')).not.toHaveClass(/stale/, { timeout: 60000 });
  await expect(page.locator('#status')).not.toHaveText(/Checking/);
}

test('checks while typing and shows the reasons at the ends of the lines', async ({ page }) => {
  await typeProof(page, 'load prop\nbool A, B\nuse A implies B\nuse A\nB\n');
  await expect(page.locator('#status')).toHaveText('Proof checked');
  await expect(page.locator('#editorHighlight .hint', { hasText: '; by 3(4)' })).toBeVisible();
  await expect(page.locator('#problemsSummary')).toContainText('No problems');
});

test('marks an error in its line and the gutter, and lists it', async ({ page }) => {
  await typeProof(page, 'load prop\nbool A, B, C\nuse A\nC\n');
  await expect(page.locator('#status')).toHaveText(/1 error/);
  await expect(page.locator('#editorHighlight .diag-err')).toHaveText('C');
  await expect(page.locator('#lineNumbers .err-num')).toHaveText('4');
  await page.locator('#problems > summary').click();
  const problem = page.locator('.problem.err');
  await expect(problem).toContainText('line 4');
  await expect(problem).toContainText('can not derive');
  await problem.click();
  await expect(page.locator('#editor')).toBeFocused();
  await expect(page.locator('#lineInfo')).toContainText('4: ProofError');
});

test('reports all errors, and a todo after an error (Kurt 0.8.1)', async ({ page }) => {
  await typeProof(page, 'load prop\nbool A, B, C\nuse A\nC\nB\ntodo A and C\n');
  await expect(page.locator('#status')).toHaveText('2 errors, 1 todo');
  await expect(page.locator('#lineNumbers .err-num')).toHaveText(['4', '5']);
  await expect(page.locator('#lineNumbers .todo-num')).toHaveText('6');
});

test('shows the details of a line on hover, and marks the lines its step uses', async ({ page }) => {
  await typeProof(page, 'load prop\nbool A, B\nuse A implies B\nuse A\nB\n');
  const box = await page.locator('#editor').boundingBox();
  const lineHeight = await page.locator('#editor').evaluate(e => parseFloat(getComputedStyle(e).lineHeight));
  await page.mouse.move(box.x + 20, box.y + 12 + 4.5 * lineHeight);
  await expect(page.locator('#tooltip')).toBeVisible();
  await expect(page.locator('#tooltip')).toContainText('premise');
  await expect(page.locator('#lineNumbers .ref-num')).toHaveText(['3', '4']);
  await expect(page.locator('#lineNumbers .self-num')).toHaveText('5');
  await page.locator('#tooltip a[data-line="3"]').click();
  await expect(page.locator('#lineInfo')).toContainText('3: use A implies B');
});

test('says what Kurt says about the line of the cursor, also on a phone', async ({ page }) => {
  await page.setViewportSize({ width: 390, height: 844 });
  await typeProof(page, 'load prop\nbool A, B\nuse A implies B\nuse A\nB\n');
  await page.locator('#editor').evaluate(e => { e.focus(); const at = e.value.indexOf('\nB') + 1; e.setSelectionRange(at, at); });
  await expect(page.locator('#lineInfo')).toContainText('5: B   ; by 3(4)');
  await page.locator('#lineInfo').click();
  await expect(page.locator('#lineInfo')).toContainText('premise');
  // the reasons right after the text, not at a column off the screen
  const hint = await page.locator('#editorHighlight .hint', { hasText: 'by 3(4)' }).boundingBox();
  expect(hint.x + hint.width).toBeLessThan(390);
});

test('keeps the indentation on Enter, and the reasons can be switched off', async ({ page }) => {
  await typeProof(page, 'load prop\nbool A\nassume A');
  await page.locator('#editor').press('End');
  await page.keyboard.press('Control+End');
  await page.keyboard.press('Enter');
  await page.keyboard.type('    A');
  await page.keyboard.press('Enter');
  await expect(page.locator('#editor')).toHaveValue('load prop\nbool A\nassume A\n    A\n    ');
  await page.locator('#viewBtn').click();
  await page.locator('#reasonsToggle').uncheck();
  await expect(page.locator('#editorHighlight .hint')).toHaveCount(0);
  await page.locator('#reasonsToggle').check();
});

test('links the repository of Kurt, and the old addresses of the playground still work', async ({ page }) => {
  await expect(page.locator('.header-link[href="https://github.com/harmeling/kurt-lang"]')).toBeVisible();
  await page.goto('/next.html#proof=dHJ1ZQo');
  await expect(page).toHaveURL(/\/#proof=dHJ1ZQo$/);
  await page.goto('/classic.html#proof=dHJ1ZQo');                   // the classic playground, retired (2026-10-12)
  await expect(page).toHaveURL(/\/#proof=dHJ1ZQo$/);
  await expect(page.locator('#editor')).toHaveValue('true\n', { timeout: 60000 });
});

test('shows the file and line being checked, and checks a loaded theory only once (Kurt 0.8.2)', async ({ page }) => {
  await page.evaluate(() => {
    window.seen = [];
    new MutationObserver(() => window.seen.push([document.querySelector('#status').textContent,
      document.querySelector('#progress').classList.contains('active')]))
      .observe(document.querySelector('#status'), { childList: true, characterData: true, subtree: true });
  });
  await typeProof(page, 'load natural\nnat n\nn = n\n');
  let seen = await page.evaluate(() => window.seen);
  const progress = seen.filter(([text, active]) => active && /^Checking \S+\.kurt · line \d+ of \d+ · file \d+ of \d+$/.test(text));
  expect(progress.some(([text]) => text.startsWith('Checking natural.kurt'))).toBe(true);
  await expect(page.locator('#progress')).not.toHaveClass(/active/);
  // a change: the theory isn't checked again
  await page.evaluate(() => { window.seen = []; });
  await typeProof(page, 'load natural\nnat n\nn = n\nn = n\n');
  seen = await page.evaluate(() => window.seen);
  expect(seen.some(([text]) => text.includes('natural.kurt'))).toBe(false);
});

test('opens an exercise, which loads its scene from theory/, and a solved part counts (Kurt 0.8.3)', async ({ page }) => {
  await page.locator('#examplesContainer .btn', { hasText: 'exercises' }).click();
  await expect(page.locator('.menu-heading', { hasText: 'knights and knaves' })).toBeVisible();
  await page.locator('.dropdown-menu .item', { hasText: '1-truth-and-lies.kurt' }).click();
  await expect(page.locator('#status')).toHaveText('Checked, 4 todos left', { timeout: 60000 });
  // part (a), solved: one todo fewer
  const text = await page.locator('#editor').inputValue();
  const solved = text.replace('proof\n    todo\nqed', 'proof\n    assume (A says S) ∧ knight(A)\n        A says S\n        knight(A)\n        knight(A) ⇔ S\n        S\nqed');
  await typeProof(page, solved);
  await expect(page.locator('#status')).toHaveText('Checked, 3 todos left');
});

test('links a file of the playground by its name, an edited one with its folder, and refuses other files', async ({ page, context }) => {
  await page.locator('#examplesContainer .btn', { hasText: 'exercises' }).click();
  await page.locator('.dropdown-menu .item', { hasText: '1-truth-and-lies.kurt' }).click();
  await expect(page.locator('#status')).toHaveText('Checked, 4 todos left', { timeout: 60000 });
  await page.locator('#fileBtn').click();
  await page.locator('#shareBtn').click();
  await expect(page).toHaveURL(/#file=exercises\/01-knights-and-knaves\/1-truth-and-lies\.kurt$/);
  const exercise = await page.locator('#editor').inputValue();
  // the link opens the file, which finds its scene in theory/
  const other = await context.newPage();
  await other.goto(page.url());
  await expect(other.locator('#status')).toHaveText('Checked, 4 todos left', { timeout: 60000 });
  await expect(other.locator('#editor')).toHaveValue(exercise);
  // edited: the text goes in the link, with the folder of the scene
  const solved = exercise.replace('proof\n    todo\nqed', 'proof\n    assume (A says S) ∧ knight(A)\n        A says S\n        knight(A)\n        knight(A) ⇔ S\n        S\nqed');
  await typeProof(page, solved);
  await page.locator('#fileBtn').click();
  await page.locator('#shareBtn').click();
  await expect(page).toHaveURL(/#proof=[\w-]+&folder=exercises\/01-knights-and-knaves\/$/);
  await other.goto(page.url());
  await expect(other.locator('#status')).toHaveText('Checked, 3 todos left', { timeout: 60000 });
  // only what the manifest lists
  await other.goto('/#file=../kurt.py');
  await expect(other.locator('#status')).toHaveText('The playground has no file ../kurt.py', { timeout: 60000 });
  await other.goto('/#file=proofs/tutorial/02-prove-an-implication.kurt');
  await expect(other.locator('#editor')).toHaveValue(/show/, { timeout: 60000 });
});

// ---- the shell and the certificate: a run of the whole proof (from the classic playground, 2026-10-12) ----

test('continues in the shell where the check stopped', async ({ page }) => {
  await typeProof(page, 'load prop\nbool A, B\nuse A\nuse A implies B\nshow A and B\nproof\n    B\n    A and C\nqed\n');
  await page.locator('#shellBtn').click();
  await expect(page.locator('#shellPrompt')).toHaveText(';[8]', { timeout: 60000 });   // the failing line
  await expect(page.locator('#shellHint')).toContainText('at the failing line');
  await expect(page.locator('#shellHint')).toContainText('A and B');                   // the next step
  await expect(page.locator('#shellInput')).toHaveValue('    ');                       // inside the proof
  await page.locator('#shellInput').pressSequentially('A and B');
  await page.locator('#shellInput').press('Enter');
  await expect(page.locator('#shellOutput')).toContainText('by and-intro(proof.kurt:3, proof.kurt:7)');
  await expect(page.locator('#shellPrompt')).toHaveText(';[9]');
  await page.locator('#shellInput').fill('qed');
  await page.locator('#shellInput').press('Enter');
  await expect(page.locator('#shellOutput')).toContainText('; by 8');
  await page.locator('#shellCopyBtn').click();                                          // before the failing line
  await expect(page.locator('#editor')).toHaveValue(/    B\n    A and B\nqed\n    A and C/);
  await page.locator('#shellCloseBtn').click();
  await expect(page.locator('#shellBar')).toBeHidden();
});

test('continues at a breakpoint, and completes with Tab in the shell', async ({ page }) => {
  await typeProof(page, 'load numbers\ncalc on\nbreakpoint\n1 + 1 = 2\n');
  await page.locator('#shellBtn').click();
  await expect(page.locator('#shellHint')).toContainText('at the breakpoint', { timeout: 60000 });
  await page.locator('#shellInput').fill('17*42=');
  await page.locator('#shellInput').press('Tab');
  await expect(page.locator('#shellInput')).toHaveValue('17*42=714');
});

test('downloads the certificate of a checked proof from the File menu, and none of a rejected one', async ({ page }) => {
  await typeProof(page, 'bool A\nuse A\nA\n');
  await page.locator('#fileBtn').click();
  for (const id of ['#loadBtn', '#saveBtn', '#shareBtn', '#certificateBtn']) await expect(page.locator(id)).toBeVisible();
  const download = page.waitForEvent('download');
  await page.locator('#certificateBtn').click();
  expect((await download).suggestedFilename()).toMatch(/\.kurtc$/);           // named after the file
  await expect(page.locator('#fileMenu')).toBeHidden();
  await typeProof(page, 'bool A, B\nuse A\nB\n');
  await page.locator('#fileBtn').click();
  await page.locator('#certificateBtn').click();
  await expect(page.locator('#status')).toHaveText(/No certificate/, { timeout: 60000 });
});

// ---- the rest of the page (from the classic playground's tests, 2026-10-12) ----------------------------

test('creates a restorable share link and keeps the draft', async ({ page, context }) => {
  await page.locator('#editor').fill('true\n');
  await page.locator('#fileBtn').click();
  await page.locator('#shareBtn').click();
  await expect(page).toHaveURL(/#proof=/);
  const other = await context.newPage();
  await other.goto(page.url());
  await expect(other.locator('#editor')).toHaveValue('true\n');
  await page.reload();
  await expect(page.locator('#editor')).toHaveValue('true\n');
});

test('offers touch symbols and registers its offline worker', async ({ page }) => {
  await page.locator('#editor').fill('');
  await page.locator('#symbolBar .symbol', { hasText: '∀' }).click();
  await expect(page.locator('#editor')).toHaveValue('∀');
  await expect.poll(() => page.evaluate(() => navigator.serviceWorker.getRegistration().then(Boolean))).toBeTruthy();
});

test('scrolls a long menu that does not fit into the window', async ({ page }) => {
  await page.setViewportSize({ width: 900, height: 500 });
  await page.locator('.menu-wrapper button', { hasText: 'keywords' }).click();
  const menu = page.locator('.menu-wrapper', { hasText: 'keywords' }).locator('.dropdown-menu');
  await expect(menu).toBeVisible();
  const box = await menu.boundingBox();
  expect(box.y + box.height).toBeLessThanOrEqual(500);
  expect(await menu.evaluate(m => m.scrollHeight > m.clientHeight)).toBeTruthy();
  const last = menu.locator('.item', { hasText: '45-builtin.kurt' });
  await last.scrollIntoViewIfNeeded();
  await last.click();
  await expect(page.locator('#editor')).toHaveValue(/45-builtin/);
});

test('checks a lesson that loads a file next to it', async ({ page }) => {
  await page.locator('.menu-wrapper button', { hasText: 'tutorial' }).click();
  const menu = page.locator('.menu-wrapper', { hasText: 'tutorial' }).locator('.dropdown-menu');
  const lesson = menu.locator('.item', { hasText: '12-write-and-load-a-reusable-theory.kurt' });
  await lesson.scrollIntoViewIfNeeded();
  await lesson.click();
  await expect(page.locator('#editor')).toHaveValue(/load my-theory/);
  await expect(page.locator('#status')).toHaveText('Proof checked', { timeout: 60000 });
});

test('opens and closes the help, which explains the shell and the certificate', async ({ page }) => {
  await page.locator('#helpBtn').click();
  const help = page.locator('#helpDialog');
  await expect(help).toBeVisible();
  await expect(help).toContainText('The shell');
  await expect(help).toContainText('certificate');
  await page.keyboard.press('Escape');
  await expect(help).toBeHidden();
  await page.locator('#helpBtn').click();
  await page.locator('#helpCloseBtn').click();
  await expect(help).toBeHidden();
});

test('changes the text size in the View menu, and keeps the menus inside a phone screen', async ({ page }) => {
  const size = () => page.evaluate(() => getComputedStyle(document.documentElement).getPropertyValue('--code-font-size').trim());
  await page.locator('#viewBtn').click();
  await page.locator('#fontResetBtn').click();
  await expect.poll(size).toBe('15px');
  await page.locator('#fontLargerBtn').click();
  await expect.poll(size).toBe('16px');
  await expect(page.locator('#fontSizeLabel')).toHaveText('16');
  await page.locator('#fontResetBtn').click();
  await page.locator('#viewBtn').click();                             // closes it
  await page.setViewportSize({ width: 390, height: 844 });            // an iPhone
  for (const [button, menu] of [['#viewBtn', '#viewMenu'], ['#fileBtn', '#fileMenu']]) {
    await page.locator(button).click();
    const box = await page.locator(menu).boundingBox();
    expect(box.x).toBeGreaterThanOrEqual(0);
    expect(box.x + box.width).toBeLessThanOrEqual(390);
    await page.locator(button).click();
  }
});

test('switches between the dark and the light theme, and remembers it', async ({ page }) => {
  const theme = () => page.evaluate(() => document.documentElement.dataset.theme);
  const first = await theme();
  await page.locator('#themeBtn').click();
  expect(await theme()).not.toBe(first);
  await page.reload();
  expect(await theme()).not.toBe(first);
  await expect(page.locator('#themeBtn')).toHaveText(first === 'dark' ? 'Dark' : 'Light');
});

test('shows the first lesson of the tutorial on a first visit, checked', async ({ page }) => {
  await expect(page.locator('#editor')).toHaveValue(/01-apply-an-implication-modus-ponens/);
  await expect(page.locator('#status')).toHaveText('Proof checked', { timeout: 60000 });
});

test('has the proofs of the course mafi1 in a menu of their own', async ({ page }) => {
  await page.locator('.menu-wrapper button', { hasText: 'mafi1' }).click();
  const menu = page.locator('.menu-wrapper', { hasText: 'mafi1' }).locator('.dropdown-menu');
  const lesson = menu.locator('.item', { hasText: '06-subspaces.kurt' });
  await lesson.scrollIntoViewIfNeeded();
  await lesson.click();
  await expect(page.locator('#editor')).toHaveValue(/load vectorspace/);
  await expect(page.locator('#status')).toHaveText('Proof checked', { timeout: 120000 });
});

test('resizes the editor and the shell with the bar between them, and puts the shell beside the editor', async ({ page }) => {
  await page.setViewportSize({ width: 1400, height: 900 });
  await typeProof(page, 'bool A\nuse A\nA\n');
  await page.locator('#shellBtn').click();
  await expect(page.locator('#shellPrompt')).toBeVisible({ timeout: 60000 });
  const box = async sel => page.locator(sel).boundingBox();
  const [shell, divider] = [await box('#shellBar'), await box('#shellDivider')];
  expect(shell.y).toBeGreaterThan((await box('.editor-panel')).y);                 // below the editor
  await page.mouse.move(divider.x + divider.width / 2, divider.y + divider.height / 2);
  await page.mouse.down(); await page.mouse.move(divider.x + divider.width / 2, divider.y - 150, { steps: 5 }); await page.mouse.up();
  expect((await box('#shellBar')).height).toBeGreaterThan(shell.height + 100);    // taller
  await page.reload();
  await expect(page.locator('#version')).toHaveText(/^Kurt \d/, { timeout: 60000 });
  await page.locator('#shellBtn').click();
  await expect(page.locator('#shellPrompt')).toBeVisible({ timeout: 60000 });
  expect((await box('#shellBar')).height).toBeGreaterThan(shell.height + 100);    // remembered
  await page.locator('#viewBtn').click();
  await page.locator('#shellSideToggle').check();
  const [editor, beside] = [await box('.editor-panel'), await box('#shellBar')];
  expect(beside.x).toBeGreaterThan(editor.x + editor.width - 1);                  // to the right
  expect(Math.abs(beside.y - editor.y)).toBeLessThan(2);
});
