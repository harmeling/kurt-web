const { defineConfig } = require('@playwright/test');
module.exports = defineConfig({
  testDir: './tests', timeout: 90000, retries: 1, workers: 1,
  use: { baseURL: 'http://127.0.0.1:8000', trace: 'retain-on-failure' },
  webServer: { command: 'python3 server.py --port 8000', port: 8000, reuseExistingServer: true }
});
