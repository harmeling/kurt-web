# Kurt Playground (static site)

A minimal, dark-mode playground for the Kurt proof language that runs fully in the browser using Pyodide.

- Write a proof on the left, click Run (or press Cmd/Ctrl+Enter) to execute `kurt.py` client-side.
- Output appears on the right (or below on small screens).
- No server required.

## Files

- `index.html` — App shell and layout.
- `styles.css` — Dark theme and responsive split-pane styling.
- `app.js` — Loads Pyodide, mounts `kurt.py`, and runs proofs by invoking Python.
- `kurt.py` — The Kurt interpreter. If this file is not present next to the site, a small fallback implementation is used that simply echoes input lines.
- `modus-ponens.kurt` — Example proof (optional).

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

Place your actual `kurt.py` file next to `index.html` (same folder). The app will fetch it and run that version. If it can't find it, the fallback is used.

## Notes

- Everything executes in the browser via WebAssembly. No server-side execution is performed.
- We can add syntax highlighting (e.g., CodeMirror/Monaco) later.
- If `kurt.py` needs any Python packages, we can load them using Pyodide's micropip at startup.

## Safari troubleshooting

- If you see `WebKitErrorDomain:305` or similar errors loading Pyodide:
  - Prefer running the included `server.py` (adds COOP/COEP headers).
  - Make sure you open `http://localhost:8000` (not `file://`).
  - In Safari Settings → Advanced, try enabling “Show features for web developers” and ensure JavaScript is allowed.
  - Hard refresh (Cmd+Shift+R) after switching servers to clear cached headers.
