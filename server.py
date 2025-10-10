#!/usr/bin/env python3
"""
Simple static server for the Kurt playground with headers for cross-origin isolation
which improves Safari/Chrome compatibility for WebAssembly and Pyodide.

Usage:
  python3 server.py --port 8000

Then open:
  http://localhost:8000/
"""

import argparse
import json
import os
from urllib.parse import urlparse, parse_qs, unquote
from http.server import ThreadingHTTPServer, SimpleHTTPRequestHandler


class KurtRequestHandler(SimpleHTTPRequestHandler):
    def end_headers(self):
        # Enable cross-origin isolation (needed for certain WebAssembly features)
        self.send_header('Cross-Origin-Opener-Policy', 'same-origin')
        self.send_header('Cross-Origin-Embedder-Policy', 'require-corp')
        # Security headers (optional but good hygiene)
        self.send_header('X-Content-Type-Options', 'nosniff')
        self.send_header('Referrer-Policy', 'strict-origin-when-cross-origin')
        # Cache control: keep it simple during development
        self.send_header('Cache-Control', 'no-store')
        super().end_headers()

    # Ensure correct MIME type for WebAssembly if any local .wasm files are present
    extensions_map = {
        **SimpleHTTPRequestHandler.extensions_map,
        '.wasm': 'application/wasm',
        '.mjs': 'text/javascript',
    }

    def do_GET(self):
        # Provide a simple JSON directory listing to help the UI discover files reliably
        if self.path.startswith('/__list'):
            parsed = urlparse(self.path)
            qs = parse_qs(parsed.query)
            rel_path = qs.get('path', [''])[0]
            rel_path = unquote(rel_path)
            # Prevent directory traversal
            if rel_path.startswith('../') or rel_path.startswith('..\\'):
                self.send_error(400, 'Invalid path')
                return
            fs_path = self.translate_path('/' + rel_path)
            if not os.path.isdir(fs_path):
                self.send_response(200)
                self.send_header('Content-Type', 'application/json')
                self.end_headers()
                self.wfile.write(json.dumps({"dirs": [], "files": []}).encode('utf-8'))
                return
            try:
                entries = os.listdir(fs_path)
                dirs = sorted([e + '/' for e in entries if os.path.isdir(os.path.join(fs_path, e))])
                files = sorted([e for e in entries if os.path.isfile(os.path.join(fs_path, e))])
                payload = {"dirs": dirs, "files": files}
                self.send_response(200)
                self.send_header('Content-Type', 'application/json')
                self.end_headers()
                self.wfile.write(json.dumps(payload).encode('utf-8'))
            except Exception as ex:
                self.send_error(500, f'Listing error: {ex}')
            return
        # Fallback to normal static handling
        return super().do_GET()


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--port', type=int, default=8000)
    args = parser.parse_args()

    server = ThreadingHTTPServer(('127.0.0.1', args.port), KurtRequestHandler)
    print(f"Serving Kurt Playground on http://127.0.0.1:{args.port}")
    print("Press Ctrl+C to stop.")
    try:
        server.serve_forever()
    except KeyboardInterrupt:
        print("\nStopping server…")


if __name__ == '__main__':
    main()
