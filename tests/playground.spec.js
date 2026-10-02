const { test, expect } = require('@playwright/test');

test.beforeEach(async ({ page }) => {
  await page.goto('/');
  await expect(page.locator('#status')).toHaveText('Ready', { timeout: 60000 });
});

test('checks a proof and loads a standard theory', async ({ page }) => {
  await page.locator('#editor').fill('load arith\ncalc on\n1 + 1 = 2\n');
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

test('scrolls a long menu that does not fit into the window', async ({ page }) => {
  await page.setViewportSize({ width: 900, height: 500 });
  await page.locator('.menu-wrapper button', { hasText: 'tutorial' }).click();
  const menu = page.locator('.menu-wrapper', { hasText: 'tutorial' }).locator('.dropdown-menu');
  await expect(menu).toBeVisible();
  const box = await menu.boundingBox();
  expect(box.y + box.height).toBeLessThanOrEqual(500);
  expect(await menu.evaluate(m => m.scrollHeight > m.clientHeight)).toBeTruthy();
  const last = menu.locator('.item', { hasText: '48-groups.kurt' });
  await last.scrollIntoViewIfNeeded();
  await last.click();
  await expect(page.locator('#editor')).toHaveValue(/48-groups/);
});

test('opens and closes the help', async ({ page }) => {
  await page.locator('#helpBtn').click();
  const help = page.locator('#helpDialog');
  await expect(help).toBeVisible();
  await expect(help).toContainText('Getting started');
  await expect(help).toContainText('Certificate');
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
  await expect(page.locator('.app-header a', { hasText: 'kurt-lang.org' })).toHaveAttribute('href', 'https://www.kurt-lang.org');
});

test('has copy, download and the certificate in the Save menu', async ({ page }) => {
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
  await expect(page.locator('#output')).toHaveText(/^A {59}; /m, { timeout: 60000 });
});
