const CACHE = 'kurt-playground-e14abd6b6216';
const ASSETS = ['./','index.html','editor.js','editor.css','classic.html','styles.css','kurt-worker.js','kurt.py','manifest.json','language.json','replacements.json','site.webmanifest','icon.svg','icon-192.png','icon-512.png','apple-touch-icon.png'];
self.addEventListener('install', event => event.waitUntil(caches.open(CACHE).then(cache => cache.addAll(ASSETS)).then(() => self.skipWaiting())));
self.addEventListener('activate', event => event.waitUntil(caches.keys().then(keys => Promise.all(keys.filter(key => key !== CACHE).map(key => caches.delete(key)))).then(() => self.clients.claim())));
self.addEventListener('fetch', event => {
  const url = new URL(event.request.url);
  if (event.request.method !== 'GET' || url.origin !== location.origin) return;
  if (url.pathname.startsWith(new URL('reference/', self.registration.scope).pathname)) return;   // the reference (MkDocs, ~1 MB): from the network, not in the offline cache
  event.respondWith(caches.match(event.request).then(cached => cached || fetch(event.request).then(response => { const copy = response.clone(); caches.open(CACHE).then(cache => cache.put(event.request, copy)); return response; })));
});
