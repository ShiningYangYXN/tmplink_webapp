var domainList = ['ttttt.link', 'tmp.link', 'static.vx-cdn.com','127.0.0.1'];

const resSet = "tmplink v2";
const assets = [
  '/',
];

self.addEventListener("install", installEvent => {
  self.skipWaiting();
  installEvent.waitUntil(
    caches.open(resSet).then(cache => {
      cache.addAll(assets);
    })
  );
});

self.addEventListener('activate', (event) => {
  event.waitUntil(
    caches.keys().then((cacheNames) => {
      return Promise.all(
        cacheNames.map((cacheName) => {
          if (cacheName !== resSet) {
            return caches.delete(cacheName);
          }
        })
      );
    })
  );
});

self.addEventListener("fetch", fetchEvent => {
  var domain = new URL(fetchEvent.request.url).hostname;
  var requestPath = new URL(fetchEvent.request.url).pathname;
  //输出日志
  if (domainList.indexOf(domain) !== -1) {
    if(requestPath !== '/index.html'||requestPath !== '/'){
      fetchEvent.respondWith(
        caches.match(fetchEvent.request).then(res => {
          return res || fetch(fetchEvent.request);
        })
      );
    }
  }
});