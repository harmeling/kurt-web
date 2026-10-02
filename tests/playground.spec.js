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
