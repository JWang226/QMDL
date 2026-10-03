window.MathJax = {
  tex: {
    inlineMath: [["\\(", "\\)"]],
    displayMath: [["\\[", "\\]"]],
    processEscapes: true,
    processEnvironments: true
  },
  options: {
    ignoreHtmlClass: ".*|",
    processHtmlClass: "arithmatex"
  }
};

function typesetMathPage() {
  const math = window.MathJax;
  if (!math.startup || !math.startup.promise || !math.typesetPromise) return;
  // Wait for startup and any preceding typeset before processing a new page.
  math.startup.promise = math.startup.promise.then(() => {
    math.typesetClear();
    math.texReset();
    return math.typesetPromise();
  });
}

function observeMathPages() {
  if (typeof document$ !== "undefined") document$.subscribe(typesetMathPage);
}

if (document.readyState === "loading") {
  document.addEventListener("DOMContentLoaded", observeMathPages, { once: true });
} else {
  observeMathPages();
}
