const CACHE = 'kurt-playground-0b4c27fbc24d';
const ASSETS = ['./','index.html','editor.js','editor.css','classic.html','styles.css','kurt-worker.js','kurt.py','manifest.json','language.json','replacements.json','site.webmanifest','icon.svg','icon-192.png','icon-512.png','apple-touch-icon.png'];
self.addEventListener('install', event => event.waitUntil(caches.open(CACHE).then(cache => cache.addAll(ASSETS)).then(() => self.skipWaiting())));
self.addEventListener('activate', event => event.waitUntil(caches.keys().then(keys => Promise.all(keys.filter(key => key !== CACHE).map(key => caches.delete(key)))).then(() => self.clients.claim())));
// the playground's own files with the headers of cross-origin isolation, which GitHub Pages can't send: then the
// page has a SharedArrayBuffer, the flag of its Cancel button (editor.js). Pyodide, from jsDelivr, is served with
// `Cross-Origin-Resource-Policy: cross-origin`. (The page that registers the service worker isn't isolated yet:
// from the next visit on; until then Cancel kills the worker, as without a SharedArrayBuffer.)
function isolated(response) {
  if (!response || response.status === 0) return response;
  const headers = new Headers(response.headers);
  headers.set('Cross-Origin-Opener-Policy', 'same-origin');
  headers.set('Cross-Origin-Embedder-Policy', 'require-corp');
  return new Response(response.body, { status: response.status, statusText: response.statusText, headers });
}
self.addEventListener('fetch', event => {
  if (event.request.method !== 'GET' || new URL(event.request.url).origin !== location.origin) return;
  event.respondWith(caches.match(event.request).then(cached => cached || fetch(event.request).then(response => { const copy = response.clone(); caches.open(CACHE).then(cache => cache.put(event.request, copy)); return response; })).then(isolated));
});
