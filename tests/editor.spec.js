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

test('links the repository of Kurt and the classic playground, and the old address of the editor still works', async ({ page }) => {
  await expect(page.locator('.header-link[href="https://github.com/harmeling/kurt-lang"]')).toBeVisible();
  await page.locator('.header-link', { hasText: 'classic' }).click();
  await expect(page).toHaveURL(/classic\.html$/);
  await page.locator('.try-next').click();
  await expect(page.locator('#lineInfo')).toBeAttached();
  await page.goto('/next.html#proof=dHJ1ZQo');
  await expect(page).toHaveURL(/\/#proof=dHJ1ZQo$/);
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
