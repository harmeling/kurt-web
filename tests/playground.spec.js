const { test, expect } = require('@playwright/test');

test.beforeEach(async ({ page }) => {
  await page.goto('/');
  await expect(page.locator('#status')).toHaveText('Ready', { timeout: 60000 });
});

test('checks a proof and loads a standard theory', async ({ page }) => {
  await page.locator('#editor').fill('load numbers\ncalc on\n1 + 1 = 2\n');
  await page.locator('#runBtn').click();
  await expect(page.locator('#status')).toHaveText('Proof checked', { timeout: 60000 });
  await expect(page.locator('#output')).toContainText('Proof checked');
  await expect(page.locator('#certificateBtn')).toBeEnabled();
});

test('rejects invalid source and links to its line', async ({ page }) => {
  await page.locator('#editor').fill('load prop\nBAD ???\n');
  await page.locator('#runBtn').click();
  await expect(page.locator('#status')).toHaveText('Proof rejected', { timeout: 60000 });
  await expect(page.locator('.diagnostic').first()).toContainText('line 2');
  await page.locator('.diagnostic').first().click();
  await expect(page.locator('#editor')).toBeFocused();
});

test('creates a restorable share link and persists a draft', async ({ page, context }) => {
  await page.locator('#editor').fill('true\n');
  await page.locator('#fileBtn').click();
  await page.locator('#shareBtn').click();
  await expect(page).toHaveURL(/#proof=/);
  const url = page.url();
  const other = await context.newPage();
  await other.goto(url);
  await expect(other.locator('#editor')).toHaveValue('true\n');
});

test('offers touch symbols and registers its offline worker', async ({ page }) => {
  await page.locator('#editor').fill('');
  await page.locator('#symbolBar .symbol', { hasText: '∀' }).click();
  await expect(page.locator('#editor')).toHaveValue('∀');
  await expect.poll(() => page.evaluate(() => navigator.serviceWorker.getRegistration().then(Boolean))).toBeTruthy();
});

test('a long menu ends inside its panel, above the footer (side by side)', async ({ page }) => {
  await page.setViewportSize({ width: 1400, height: 700 });
  await page.locator('.menu-wrapper button', { hasText: 'keywords' }).click();
  const menu = page.locator('.menu-wrapper', { hasText: 'keywords' }).locator('.dropdown-menu');
  await expect(menu).toBeVisible();
  const box = await menu.boundingBox();
  const panel = await page.locator('.editor-panel').boundingBox();
  expect(box.y + box.height).toBeLessThanOrEqual(panel.y + panel.height);
  // scrolled to its end, the last item is inside the panel too, not cut off by it
  await menu.evaluate(m => { m.scrollTop = m.scrollHeight; });
  const last = await menu.locator('.item', { hasText: '45-builtin.kurt' }).boundingBox();
  expect(last.y + last.height).toBeLessThanOrEqual(panel.y + panel.height);
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

test('runs a lesson that loads a file next to it', async ({ page }) => {
  // lesson 12 of the tutorial loads `my-theory.kurt` from its folder -- the playground has to
  // give it to the worker along with the proof
  await page.locator('.menu-wrapper button', { hasText: 'tutorial' }).click();
  const menu = page.locator('.menu-wrapper', { hasText: 'tutorial' }).locator('.dropdown-menu');
  const lesson = menu.locator('.item', { hasText: '12-write-and-load-a-reusable-theory.kurt' });
  await lesson.scrollIntoViewIfNeeded();
  await lesson.click();
  await expect(page.locator('#editor')).toHaveValue(/load my-theory/);
  await page.locator('#runBtn').click();
  await expect(page.locator('#status')).toHaveText('Proof checked', { timeout: 60000 });
});

test('marks the lines a step uses when hovering its line in the output', async ({ page }) => {
  await page.locator('#editor').fill('bool A, B\nuse A implies B\nuse A\nB\n');
  await page.locator('#runBtn').click();
  await expect(page.locator('#status')).toHaveText('Proof checked', { timeout: 60000 });
  const step = page.locator('#output .output-line', { hasText: 'by 2(3)' });
  await step.hover();
  await expect(step).toHaveClass(/self/);
  // the mark starts after the gutter (as in the editor), the number's box is the gutter's color
  expect(await step.evaluate(r => getComputedStyle(r).backgroundImage)).toContain('linear-gradient');
  expect(await step.evaluate(r => getComputedStyle(r, '::before').backgroundColor))
    .toBe(await page.locator('#lineNumbers').evaluate(g => getComputedStyle(g).backgroundColor));
  await expect(page.locator('#output .output-line.ref')).toHaveCount(2);          // lines 2 and 3
  await expect(page.locator('#editorHighlight .ref-line')).toHaveCount(2);
  await expect(page.locator('#editorHighlight .self-line')).toHaveCount(1);       // line 4
  await expect(page.locator('#lineNumbers .ref-num')).toHaveText(['2', '3']);     // their numbers
  await expect(page.locator('#lineNumbers .self-num')).toHaveText('4');
  await page.locator('#editor').hover();
  await expect(page.locator('#output .output-line.ref')).toHaveCount(0);
});

test('opens and closes the help', async ({ page }) => {
  await page.locator('#helpBtn').click();
  const help = page.locator('#helpDialog');
  await expect(help).toBeVisible();
  await expect(help).toContainText('Getting started');
  await expect(help).toContainText('certificate');
  await page.keyboard.press('Escape');
  await expect(help).toBeHidden();
  await page.locator('#helpBtn').click();
  await page.locator('#helpCloseBtn').click();
  await expect(help).toBeHidden();
});

test('has upload, download and the link in the File menu', async ({ page }) => {
  await expect(page.locator('#loadBtn')).toBeHidden();
  await page.locator('#fileBtn').click();
  for (const id of ['#loadBtn', '#saveBtn', '#shareBtn']) await expect(page.locator(id)).toBeVisible();
  const download = page.waitForEvent('download');
  await page.locator('#saveBtn').click();
  expect((await download).suggestedFilename()).toMatch(/\.kurt$/);
  await expect(page.locator('#fileMenu')).toBeHidden();
  await expect(page.locator('.app-header a', { hasText: 'github.com/harmeling/kurt-lang' })).toHaveAttribute('href', 'https://github.com/harmeling/kurt-lang');
});

test('has copy, download and the certificate in the File menu of the output', async ({ page }) => {
  await page.locator('#editor').fill('bool A\nuse A\nA\n');
  await page.locator('#runBtn').click();
  await expect(page.locator('#status')).toHaveText('Proof checked', { timeout: 60000 });
  await page.locator('#saveOutputBtn').click();
  for (const id of ['#copyBtn', '#outputDownloadBtn', '#certificateBtn']) await expect(page.locator(id)).toBeVisible();
  await expect(page.locator('#certificateBtn')).toBeEnabled();
  const download = page.waitForEvent('download');
  await page.locator('#certificateBtn').click();
  expect((await download).suggestedFilename()).toBe('proof.kurtc');
  await expect(page.locator('#saveOutputMenu')).toBeHidden();
});

test('changes the text size and the column of the reasons in the View menu', async ({ page }) => {
  const size = () => page.evaluate(() => getComputedStyle(document.documentElement).getPropertyValue('--code-font-size').trim());
  await page.locator('#viewBtn').click();
  await page.locator('#fontResetBtn').click();
  await expect.poll(size).toBe('15px');
  await page.locator('#fontLargerBtn').click();
  await expect.poll(size).toBe('16px');
  await expect(page.locator('#fontSizeLabel')).toHaveText('16');
  await page.locator('#fontResetBtn').click();
  await page.locator('#editor').fill('bool A\nuse A\nA\n');
  await page.locator('#runBtn').click();
  await expect(page.locator('#status')).toHaveText('Proof checked', { timeout: 60000 });
  await page.locator('#viewBtn').click();
  // (Playwright can't `fill` a range input: set it like a drag does, with `input` and `change`)
  await page.locator('#indentSlider').evaluate(slider => {
    slider.value = '60';
    slider.dispatchEvent(new Event('input', { bubbles: true }));
    slider.dispatchEvent(new Event('change', { bubbles: true }));   // checks the proof again with the new column
  });
  await expect(page.locator('#indentLabel')).toHaveText('60');
  // (the output has a line per element, without line breaks in its text: no `^`)
  await expect(page.locator('#output')).toHaveText(/A {59}; by 2/, { timeout: 60000 });
});

test('keeps the menus inside a phone screen', async ({ page }) => {
  await page.setViewportSize({ width: 390, height: 844 });            // an iPhone
  for (const [button, menu] of [['#viewBtn', '#viewMenu'], ['#fileBtn', '#fileMenu']]) {
    await page.locator(button).click();
    const box = await page.locator(menu).boundingBox();
    expect(box.x).toBeGreaterThanOrEqual(0);
    expect(box.x + box.width).toBeLessThanOrEqual(390);
    await page.locator(button).click();                               // closes it again
  }
});

test('shows line numbers that scroll with the editor', async ({ page }) => {
  await page.locator('#editor').fill('bool A\nuse A\nA\n');
  await expect(page.locator('#lineNumbers')).toHaveText('1\n2\n3\n4');
  const many = Array.from({ length: 200 }, (_, i) => `; line ${i + 1}`).join('\n');
  await page.locator('#editor').fill(many);
  await expect(page.locator('#lineNumbers')).toContainText('200');
  // the editor's text, its highlighted copy and the numbers scroll together, in one container
  await page.locator('#editorWrap').evaluate(w => { w.scrollTop = w.scrollHeight; });
  const y = async sel => (await page.locator(sel).boundingBox()).y;
  expect(await y('#editor')).toBeLessThan(await y('#editorWrap') - 600);
  expect(await y('#editorHighlight')).toBe(await y('#editor'));
  expect(await y('#lineNumbers')).toBe(await y('#editor'));
  expect(await page.locator('#editor').evaluate(e => e.scrollTop)).toBe(0);
  // typing at the end: the textarea doesn't scroll on its own, the container shows the caret
  const scrolled = () => page.locator('#editorWrap').evaluate(w => [w.scrollTop, w.scrollLeft]);
  const before = await scrolled();
  await page.locator('#editor').focus();
  await page.keyboard.press('Control+End');
  for (let i = 0; i < 5; i++) await page.keyboard.press('Enter');
  await page.keyboard.type('; the end, a long line ' + 'x'.repeat(200));
  expect(await page.locator('#editor').evaluate(e => [e.scrollTop, e.scrollLeft])).toEqual([0, 0]);
  const [wrap, highlight, editor] = [await page.locator('#editorWrap').boundingBox(), await page.locator('#editorHighlight').boundingBox(), await page.locator('#editor').boundingBox()];
  expect(highlight.y).toBe(editor.y); expect(highlight.x).toBe(editor.x);
  const after = await scrolled();
  expect(after[0]).toBeGreaterThan(before[0]); expect(after[1]).toBeGreaterThan(before[1]);   // to the caret
});

test('fills the window, aligns the first lines, and moves the divider', async ({ page }) => {
  await page.setViewportSize({ width: 1600, height: 900 });
  await expect(page.locator('#divider')).toBeHidden();                            // no output yet
  await page.locator('#editor').fill('bool A\nuse A\nA\n');
  await page.locator('#runBtn').click();
  await expect(page.locator('#status')).toHaveText('Proof checked', { timeout: 60000 });
  const box = async sel => page.locator(sel).boundingBox();
  const [editor, output, divider] = [await box('#editorWrap'), await box('#output'), await box('#divider')];
  expect(editor.x).toBeLessThan(20); expect(output.x + output.width).toBeGreaterThan(1580);
  expect(Math.abs(editor.y - output.y)).toBeLessThan(1.5);                        // the first lines
  const [left, right] = [await box('.editor-panel'), await box('#outputPanel')];
  expect(Math.abs(left.y + left.height - right.y - right.height)).toBeLessThan(1.5); // the bottoms
  await page.mouse.move(divider.x + divider.width / 2, divider.y + divider.height / 2);
  await page.mouse.down(); await page.mouse.move(500, divider.y + divider.height / 2, { steps: 5 }); await page.mouse.up();
  expect((await box('#editorWrap')).width).toBeLessThan(editor.width - 200);
  await page.reload(); await expect(page.locator('#status')).toHaveText('Ready', { timeout: 60000 });
  await page.locator('#runBtn').click();
  await expect(page.locator('#status')).toHaveText('Proof checked', { timeout: 60000 });
  expect((await box('#editorWrap')).width).toBeLessThan(editor.width - 200);     // remembered
  await page.locator('#divider').dblclick();
  expect(Math.abs((await box('#editorWrap')).width - editor.width)).toBeLessThan(2);
});

test('numbers the lines of the output that echo a line of the editor', async ({ page }) => {
  await page.locator('#editor').fill('; a lemma\nbool A, B\nshow A implies A\nproof\n  assume A\n    A\nqed\n');
  await page.locator('#runBtn').click();
  await expect(page.locator('#status')).toHaveText('Proof checked', { timeout: 60000 });
  const numbered = page.locator('#output .output-line[data-line]');
  const lines = await numbered.evaluateAll(rows => rows.map(r => [r.dataset.line, r.textContent.split(';')[0].trim()]));
  // the gutter is the background of the whole output, not only of the numbers (both themes)
  for (const theme of ['dark', 'light']) {
    await page.evaluate(t => { document.documentElement.dataset.theme = t; }, theme);
    const image = await page.locator('#output').evaluate(o => getComputedStyle(o).backgroundImage);
    expect(image).toContain('linear-gradient');
    const border = await page.evaluate(() => { const d = document.createElement('div'); d.style.color = 'var(--border)'; document.body.append(d); const c = getComputedStyle(d).color; d.remove(); return c; });
    expect(image).not.toContain(border);                                          // no dividing line (it fell between pixels)
  }
  expect(lines).toEqual([['3', 'show A implies A'], ['4', 'proof'], ['5', 'assume A'], ['6', 'A'], ['7', 'qed']]);
});

test('switches between the dark and the light theme, and remembers it', async ({ page }) => {
  const theme = () => page.evaluate(() => document.documentElement.dataset.theme);
  const background = () => page.locator('.editor-wrap').evaluate(e => getComputedStyle(e).backgroundColor);
  const first = await theme(), before = await background();
  expect(before).not.toBe('rgba(0, 0, 0, 0)');                                    // every color is defined
  for (const name of ['--code-bg', '--gutter-bg', '--bar-bg', '--btn-bg', '--mark-self', '--tok-kw1'])
    expect(await page.evaluate(n => getComputedStyle(document.documentElement).getPropertyValue(n).trim(), name)).not.toBe('');
  await page.locator('#themeBtn').click();
  expect(await theme()).not.toBe(first);
  expect(await background()).not.toBe(before);
  expect(await background()).not.toBe('rgba(0, 0, 0, 0)');
  await page.reload();
  expect(await theme()).not.toBe(first);
  await expect(page.locator('#themeBtn')).toHaveText(first === 'dark' ? 'Dark' : 'Light');
});

test('has the symbols below the editor', async ({ page }) => {
  const bar = await page.locator('#symbolBar').boundingBox(), editor = await page.locator('#editorWrap').boundingBox();
  expect(bar.y).toBeGreaterThanOrEqual(editor.y + editor.height - 1);
});

test('clears the output when another file is loaded', async ({ page }) => {
  await page.locator('#editor').fill('bool A\nuse A\nA\n');
  await page.locator('#runBtn').click();
  await expect(page.locator('#status')).toHaveText('Proof checked', { timeout: 60000 });
  await expect(page.locator('#outputPanel')).toBeVisible();
  await page.locator('.menu-wrapper button', { hasText: 'tutorial' }).click();
  await page.locator('.menu-wrapper', { hasText: 'tutorial' }).locator('.dropdown-menu .item').first().click();
  await expect(page.locator('#outputPanel')).toBeHidden();
  await expect(page.locator('#output')).toHaveText('');
  await expect(page.locator('#certificateBtn')).toBeDisabled();
});

test('marks the block a result comes from, and the block a step uses', async ({ page }) => {
  await page.locator('#editor').fill('load prop\nbool A, B, C\nuse A or B\nuse A implies C\nuse B implies C\ncase A\n    C\ncase B\n    C\nC\n');
  await page.locator('#runBtn').click();
  await expect(page.locator('#status')).toHaveText('Proof checked', { timeout: 60000 });
  const result = page.locator('#output .output-line', { hasText: '; 6-7 by impl-intro' });
  await result.hover();
  await expect(page.locator('#lineNumbers .ref-num')).toHaveText(['6', '7']);     // its block
  const step = page.locator('#output .output-line', { hasText: 'by case-elim' });
  await step.hover();
  await expect(page.locator('#output .output-line.ref', { hasText: '; 6-7 by impl-intro' })).toHaveCount(1);
  await expect(page.locator('#output .output-line.ref', { hasText: '; 8-9 by impl-intro' })).toHaveCount(1);
  await expect(page.locator('#lineNumbers .self-num')).toHaveText('10');
});

test('has the proofs of the course mafi1 in a menu of their own', async ({ page }) => {
  // (the menu comes with the update of kurt.py after 0.7.4, whose theories the files load)
  test.skip(await page.locator('.menu-wrapper button', { hasText: 'mafi1' }).count() === 0, 'no mafi1 menu yet');
  await page.locator('.menu-wrapper button', { hasText: 'mafi1' }).click();
  const menu = page.locator('.menu-wrapper', { hasText: 'mafi1' }).locator('.dropdown-menu');
  const lesson = menu.locator('.item', { hasText: '06-subspaces.kurt' });
  await lesson.scrollIntoViewIfNeeded();
  await lesson.click();
  await expect(page.locator('#editor')).toHaveValue(/load vectorspace/);
  await page.locator('#runBtn').click();
  await expect(page.locator('#status')).toHaveText('Proof checked', { timeout: 120000 });
});

test('shows the first lesson of the tutorial on a first visit', async ({ page }) => {
  await expect(page.locator('#editor')).toHaveValue(/01-apply-an-implication-modus-ponens/);
  await page.locator('#runBtn').click();
  await expect(page.locator('#status')).toHaveText('Proof checked', { timeout: 60000 });
});

test('fills the window: side by side the whole height, stacked the whole width', async ({ page }) => {
  await page.setViewportSize({ width: 1400, height: 1000 });
  await page.locator('#runBtn').click();
  await expect(page.locator('#status')).toHaveText('Proof checked', { timeout: 60000 });
  const box = async sel => page.locator(sel).boundingBox();
  const [editor, output, footer] = [await box('.editor-panel'), await box('#outputPanel'), await box('.app-footer')];
  expect(footer.y + footer.height).toBeGreaterThan(1000 - 2);                     // the page is the window
  expect(footer.y + footer.height).toBeLessThan(1000 + 2);
  expect(footer.y - (editor.y + editor.height)).toBeLessThan(40);                 // the panels reach down to the footer
  expect(Math.abs(editor.y + editor.height - output.y - output.height)).toBeLessThan(2);
  await page.setViewportSize({ width: 700, height: 1000 });
  const [narrowEditor, narrowOutput] = [await box('.editor-panel'), await box('#outputPanel')];
  expect(narrowEditor.width).toBeGreaterThan(700 - 30);                           // the whole width (12px margins)
  expect(narrowOutput.width).toBeGreaterThan(700 - 30);
  expect(narrowOutput.y).toBeGreaterThan(narrowEditor.y + narrowEditor.height - 1);   // below it
});

test('continues in the shell where the check stopped', async ({ page }) => {
  await page.locator('#editor').fill('load prop\nbool A, B\nuse A\nuse A implies B\nshow A and B\nproof\n    B\n    A and C\nqed\n');
  await page.locator('#runBtn').click();
  await expect(page.locator('#status')).toHaveText('Proof rejected', { timeout: 60000 });
  await page.locator('#shellBtn').click();
  await expect(page.locator('#shellPrompt')).toHaveText(';[8]');                      // the failing line
  await expect(page.locator('#shellHint')).toContainText('at the failing line');
  await expect(page.locator('#shellHint')).toContainText('A and B');                   // the next step
  await expect(page.locator('#shellInput')).toHaveValue('    ');                       // inside the proof
  await page.locator('#shellInput').pressSequentially('A and B');
  await page.locator('#shellInput').press('Enter');
  await expect(page.locator('#output')).toContainText('by and-intro(proof.kurt:3, proof.kurt:7)');
  await expect(page.locator('#shellPrompt')).toHaveText(';[9]');
  await page.locator('#shellInput').fill('qed');
  await page.locator('#shellInput').press('Enter');
  await expect(page.locator('#output')).toContainText('qed                                     ; by 8');
  await page.locator('#shellCopyBtn').click();                                          // before the failing line
  await expect(page.locator('#editor')).toHaveValue(/    B\n    A and B\nqed\n    A and C/);
});

test('opens the shell at a breakpoint, and completes with Tab', async ({ page }) => {
  await page.locator('#editor').fill('load numbers\ncalc on\nbreakpoint\n1 + 1 = 2\n');
  await page.locator('#runBtn').click();
  await expect(page.locator('#status')).toHaveText('Proof checked', { timeout: 60000 });
  await expect(page.locator('#shellBar')).toBeVisible();                               // opened by itself
  await expect(page.locator('#shellHint')).toContainText('at the breakpoint');
  await page.locator('#shellInput').fill('17*42=');
  await page.locator('#shellInput').press('Tab');
  await expect(page.locator('#shellInput')).toHaveValue('17*42=714');
});

test('hints and completes in the proof editor with Tab', async ({ page }) => {
  const editor = page.locator('#editor');
  await editor.fill('load numbers\ncalc on\n17*42=');
  await expect(page.locator('#editorHint')).toContainText('714', { timeout: 60000 });
  await editor.press('Tab');
  await expect(editor).toHaveValue('load numbers\ncalc on\n17*42=714');
});
