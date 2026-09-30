# Kurt Playground (static site)

A minimal, dark-mode playground for the Kurt proof language that runs fully in the browser using Pyodide.

- Write a proof on the left, click Run (or press Cmd/Ctrl+Enter) to execute `kurt.py` client-side.
- Output appears on the right (or below on small screens).
- No server required.

## Files

- `index.html` — App shell and layout.
- `styles.css` — Dark theme and responsive split-pane styling.
- `app.js` — Loads Pyodide, mounts `kurt.py`, and runs proofs by invoking Python.
- `kurt.py` — The Kurt interpreter. This is the generated Kurt 0.9 standalone bundle, including all standard theories.
- `proofs/` and `theories/` — Current examples, tutorials, and standard theories.

## Local development

You can open `index.html` directly, but some browsers block `fetch()` of local files. To avoid issues—especially on Safari—serve the folder with the included Python server which sets helpful headers.

### Option 1: Python server (recommended; Safari-friendly)

```bash
cd kurt-web
python3 server.py --port 8000
# then open http://localhost:8000
```

### Option 2: Python's SimpleHTTPServer

```bash
cd kurt-web
python3 -m http.server 8000
# then open http://localhost:8000
```

### Option 3: Node (optional)

```bash
npm -g install serve
cd kurt-web
serve -p 8000
```

## Using your real kurt.py

Run `./update.sh ../kurt-lang` to regenerate `kurt.py`, synchronize theories and tutorials, regenerate the manifest, and run smoke tests. The script deliberately does not commit or push.

## Notes

- Everything executes in the browser via WebAssembly. No server-side execution is performed.
- The editor highlights current Kurt commands, constants, variables, numbers, strings, and comments.
- If `kurt.py` needs any Python packages, we can load them using Pyodide's micropip at startup.

## Safari troubleshooting

- If you see `WebKitErrorDomain:305` or similar errors loading Pyodide:
  - Prefer running the included `server.py` (adds COOP/COEP headers).
  - Make sure you open `http://localhost:8000` (not `file://`).
  - In Safari Settings → Advanced, try enabling “Show features for web developers” and ensure JavaScript is allowed.
  - Hard refresh (Cmd+Shift+R) after switching servers to clear cached headers.

## Deploying on GitHub Pages

This site is fully static and can be hosted on GitHub Pages without any server.

- A GitHub Actions workflow (`.github/workflows/pages.yml`) builds and deploys the site to Pages on every push to `main`.
- Directory listings for examples/tutorial/theories use a static `manifest.json` fallback when the dev server endpoint is not available. The workflow auto-generates `manifest.json` during the build by scanning `proofs/` and `theories/`.

To enable Pages:

1. Push to `main` (the workflow runs automatically).
2. In your repository settings → Pages, set Source to "GitHub Actions".
3. After the first successful run, your site will be available at the URL shown in the workflow summary.

If you serve the files from any static host (e.g., GitHub Pages, Netlify), the app will use `manifest.json` to populate the menus and will run Kurt in-browser via Pyodide as usual. The Python dev server is only needed for local development.

### Quick enable steps

- Open Settings → Pages: [https://github.com/harmeling/kurt-web/settings/pages](https://github.com/harmeling/kurt-web/settings/pages)
- Set Source to "GitHub Actions" and Save.
- Watch the deployment run here: [https://github.com/harmeling/kurt-web/actions](https://github.com/harmeling/kurt-web/actions)
- Your site will be published at: [https://harmeling.github.io/kurt-web/](https://harmeling.github.io/kurt-web/)

## Playground features

Proof checking runs in a cancellable Web Worker, so the editor stays responsive. Drafts and display settings are saved locally. Share creates a URL containing the proof; no proof is uploaded. Successful runs expose downloadable output and `.kurtc` certificates. Error locations jump back to the relevant source line. The symbol strip is designed for touch screens, and the app can be installed from browsers that support PWAs.

The service worker caches the app shell and Kurt bundle. Pyodide is loaded from jsDelivr and must have been fetched by the browser at least once before an offline session.

## Tests

- `python3 scripts/smoke_test.py` checks generated assets and the standalone runtime.
- `npm install && npx playwright install chromium && npm run test:e2e` runs the real browser suite.
- `./update.sh ../kurt-lang` rebuilds Kurt, synchronizes proofs/theories, regenerates language metadata and the manifest, then runs smoke tests.
