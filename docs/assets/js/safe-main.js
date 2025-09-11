(function () {
  'use strict';

  var Safe = {
    log: function () { if (window && window.console) console.log.apply(console, arguments); },
    error: function () { if (window && window.console) console.error.apply(console, arguments); },
    safeExecute: function (fn, fallback) {
      if (typeof fn !== 'function') return;
      try { return fn(); } catch (e) { Safe.error('Error in', fn.name || 'anonymous', e); if (typeof fallback === 'function') try { fallback(e); } catch(_){} }
    }
  };

  function addHeadingIds() {
    var headings = document.querySelectorAll('h1, h2, h3, h4, h5, h6');
    var n = 0;
    for (var i = 0; i < headings.length; i++) {
      var h = headings[i];
      if (!h.id || h.id.trim() === '') {
        h.id = 'heading-' + (n++);
      }
    }
  }

  function generateTOC() {
    var toc = document.querySelector('.page-toc');
    if (!toc) return;
    var list = document.createElement('ul');
    var hs = document.querySelectorAll('h2, h3');
    for (var i = 0; i < hs.length; i++) {
      var h = hs[i];
      if (!h.id) h.id = 'toc-' + i;
      var li = document.createElement('li');
      var a = document.createElement('a');
      a.textContent = h.textContent || ('Section ' + (i + 1));
      a.href = '#' + h.id;
      li.appendChild(a); list.appendChild(li);
    }
    toc.innerHTML = ''; toc.appendChild(list);
  }

  function handleExternalLinks() {
    var as = document.querySelectorAll('a[href^="http"]:not([target])');
    for (var i = 0; i < as.length; i++) { as[i].setAttribute('target', '_blank'); as[i].setAttribute('rel', 'noopener'); }
  }

  function enhanceImages() {
    var imgs = document.querySelectorAll('img');
    for (var i = 0; i < imgs.length; i++) {
      var img = imgs[i];
      if (!img.getAttribute('alt')) {
        var src = img.getAttribute('src') || '';
        var fn = src.split('/').pop() || '';
        img.setAttribute('alt', fn.replace(/\.[a-zA-Z0-9]+$/, '') || 'image');
      }
    }
  }

  function initSmoothScrolling() {
    if ('scrollBehavior' in document.documentElement.style) return; // modern browsers ok
    // minimal polyfill or no-op
  }

  function init() {
    // Core features immediately but safely
    Safe.safeExecute(initSmoothScrolling);
    // Defer potentially heavy operations
    setTimeout(function () {
      Safe.safeExecute(addHeadingIds);
      Safe.safeExecute(generateTOC);
      Safe.safeExecute(handleExternalLinks);
      Safe.safeExecute(enhanceImages);
    }, 100);
  }

  if (document.readyState === 'loading') {
    document.addEventListener('DOMContentLoaded', function () { Safe.safeExecute(init); });
  } else {
    Safe.safeExecute(init);
  }

  // expose minimal API for extensions
  window.BookFormatterSafe = Safe;
})();
