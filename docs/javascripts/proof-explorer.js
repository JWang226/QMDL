/* Copyright (c) 2026 Free Entropy formalization contributors.
   See LICENSE and NOTICE in the repository root for license and attribution. */
/* Vanilla DOM only. Catalog text is never interpreted as HTML. */
(function () {
  "use strict";
  if (window.__qmdlProofExplorer) return;
  window.__qmdlProofExplorer = true;

  const SOURCE_BASE = "https://github.com/JWang226/Quantum-Minimum-Description-Length/blob/main/";
  const FALLBACK_CATALOG = new URL("../assets/lean-catalog.json", document.currentScript.src).href;
  const PAGE_SIZE = 80;
  const requests = new Map();
  const controllers = new WeakMap();
  let active = null;

  function el(tag, className, text) {
    const node = document.createElement(tag);
    if (className) node.className = className;
    if (text !== undefined) node.textContent = text;
    return node;
  }
  function button(text, handler, className) {
    const node = el("button", className || "pe-button", text);
    node.type = "button";
    node.addEventListener("click", handler);
    return node;
  }
  function hrefFor(kind, name) {
    return "#" + kind + "=" + encodeURIComponent(name);
  }
  function shortName(name) {
    return name.replace(/^FreeEntropy\./, "");
  }
  function sourceURL(file, line) {
    if (typeof file !== "string" || !file || file.includes("..") || file.startsWith("/")) return null;
    const path = file.split("/").map(encodeURIComponent).join("/");
    return SOURCE_BASE + path + (Number.isInteger(line) && line > 0 ? "#L" + line : "");
  }
  function sourceLink(file, line, label) {
    const url = sourceURL(file, line);
    if (!url) return el("span", "pe-muted", "Source location unavailable");
    const link = el("a", "", label || "View Lean source ↗");
    link.href = url;
    return link;
  }
  function names(value) {
    return Array.isArray(value) ? value.filter((x) => typeof x === "string") : [];
  }
  function makeModel(data) {
    if (data.version !== 1 || !Array.isArray(data.declarations) || !Array.isArray(data.modules)) {
      throw new Error("The declaration catalog has an unsupported format.");
    }
    const publicNodes = data.declarations.map((node) => ({ ...node, supplemental: false }));
    const auxiliary = (data.auxiliary_declarations || []).map((node) => ({ ...node, supplemental: true }));
    const all = [...publicNodes, ...auxiliary];
    const byName = new Map();
    const byModule = new Map();
    const usedBy = new Map();
    for (const node of all) {
      if (typeof node.name !== "string" || typeof node.statement !== "string") {
        throw new Error("A catalog declaration is missing its name or kernel type.");
      }
      node.dependencies = [...new Set(names(node.dependencies))];
      node.external_dependencies = [...new Set(names(node.external_dependencies))];
      node.search = [node.name, node.module || "", node.kind || ""].join(" ").toLowerCase();
      byName.set(node.name, node);
      if (!byModule.has(node.module)) byModule.set(node.module, []);
      byModule.get(node.module).push(node);
    }
    for (const node of all) {
      for (const dependency of node.dependencies) {
        if (!usedBy.has(dependency)) usedBy.set(dependency, []);
        usedBy.get(dependency).push(node.name);
      }
    }
    const compare = (a, b) => a.name.localeCompare(b.name);
    publicNodes.sort(compare);
    auxiliary.sort(compare);
    all.sort(compare);
    for (const list of usedBy.values()) list.sort();
    for (const list of byModule.values()) list.sort(compare);
    const modules = [...data.modules].sort(compare);
    return { data, publicNodes, auxiliary, all, byName, byModule, usedBy, modules,
      moduleByName: new Map(modules.map((m) => [m.name, m])) };
  }
  function loadCatalog(url) {
    if (!requests.has(url)) {
      const request = fetch(url, { credentials: "same-origin" })
        .then((response) => {
          if (!response.ok) throw new Error("The catalog request returned HTTP " + response.status + ".");
          return response.json();
        }).then(makeModel)
        .catch((error) => { requests.delete(url); throw error; });
      requests.set(url, request);
    }
    return requests.get(url);
  }

  function startExplorer(root, model) {
    const initialHash = location.hash.slice(1);
    const initialParams = new URLSearchParams(initialHash);
    const explicitSelection = initialParams.has("declaration") || initialParams.has("decl") || initialParams.has("module") || initialHash.startsWith("FreeEntropy.");
    const state = { view: "declarations", limit: PAGE_SIZE, selected: null, focusSelection: explicitSelection, timer: null };
    root.replaceChildren();
    root.setAttribute("aria-busy", "false");
    const ui = { root, model, state };
    controllers.set(root, ui);
    active = ui;

    function declarationLink(name, className, label) {
      const link = el("a", className || "", label || shortName(name));
      link.href = hrefFor("declaration", name);
      link.title = name;
      link.dataset.declaration = name;
      return link;
    }
    function moduleLink(name, label) {
      const link = el("a", "", label || name);
      link.href = hrefFor("module", name);
      link.title = name;
      return link;
    }
    ui.declarationLink = declarationLink;
    root.addEventListener("click", (event) => {
      const link = event.target.closest("a[href^='#declaration='], a[href^='#module=']");
      if (link && !event.ctrlKey && !event.metaKey && !event.shiftKey && !event.altKey) {
        state.focusSelection = true;
        if (link.hash === location.hash) selectFromHash();
      }
    });

    const landmarks = el("section", "pe-landmarks");
    landmarks.setAttribute("aria-label", "Main proof landmarks");
    const supportingLandmarks = el("div", "pe-landmarks");
    const fallback = [
      { title: "Theorem 1 · achievability", names: ["FreeEntropy.theorem1_achievability"] },
      { title: "Theorem 1 · converse", names: ["FreeEntropy.theorem1_converse", "FreeEntropy.theorem1_converse_of_uniform"] },
      { title: "Theorem 2 · original cloning maps", names: ["FreeEntropy.ExteriorRepresentation.theorem2_cloning_accuracy_choi"] }
    ];
    const primaryIds = new Set(["theorem1-achievability", "theorem1-converse-average", "theorem1-converse-uniform", "theorem2-choi"]);
    for (const landmark of model.data.landmarks || fallback) {
      const present = names(landmark.names).filter((name) => model.byName.has(name));
      if (!present.length) continue;
      const card = el("div", "pe-landmark");
      card.append(el("h3", "", landmark.title));
      for (const name of present) card.append(declarationLink(name));
      (landmark.id && !primaryIds.has(landmark.id) ? supportingLandmarks : landmarks).append(card);
    }
    if (landmarks.childElementCount) root.append(landmarks);
    if (supportingLandmarks.childElementCount) {
      const supporting = el("details");
      supporting.append(el("summary", "", "Supporting landmarks and definitions (" + supportingLandmarks.childElementCount + ")"));
      const body = el("div", "pe-details-body");
      body.append(supportingLandmarks);
      supporting.append(body);
      root.append(supporting);
    }

    const controls = el("div", "pe-controls");
    const searchLabel = el("label", "pe-search-label", "Find a declaration or module");
    searchLabel.htmlFor = "pe-search";
    const search = el("input");
    search.type = "search";
    search.id = "pe-search";
    search.placeholder = "Name, namespace, or module…";
    search.autocomplete = "off";
    search.spellcheck = false;
    search.setAttribute("aria-controls", "pe-results");
    const filters = el("div", "pe-filters");
    const toggles = el("div", "pe-toggle");
    toggles.setAttribute("aria-label", "Browse mode");
    const declarationsButton = button("Declarations", () => changeView("declarations"));
    const modulesButton = button("Modules", () => changeView("modules"));
    toggles.append(declarationsButton, modulesButton);
    function selectControl(label, id, options) {
      const container = el("div", "pe-filter");
      const fieldLabel = el("label", "", label);
      fieldLabel.htmlFor = id;
      const select = el("select");
      select.id = id;
      for (const [value, text] of options) {
        const option = el("option", "", text);
        option.value = value;
        select.append(option);
      }
      container.append(fieldLabel, select);
      filters.append(container);
      return { container, select };
    }
    filters.append(toggles);
    const scope = selectControl("Declaration set", "pe-scope", [
      ["public", "Source-indexed"], ["all", "All catalog nodes"], ["supplemental", "Supplemental only"]
    ]);
    const kind = selectControl("Kind", "pe-kind", [["", "All kinds"], ...[...new Set(model.all.map((n) => n.kind).filter(Boolean))].sort().map((k) => [k, k])]);
    const module = selectControl("Module", "pe-module", [["", "All modules"], ...model.modules.map((m) => [m.name, m.name.replace(/^FreeEntropy\./, "")])]);
    filters.append(button("Reset filters", () => {
      search.value = ""; scope.select.value = "public"; kind.select.value = ""; module.select.value = "";
      state.limit = PAGE_SIZE; renderResults();
    }));
    const status = el("p", "pe-status pe-muted");
    status.setAttribute("role", "status");
    status.setAttribute("aria-live", "polite");
    controls.append(searchLabel, search, filters, status);
    root.append(controls);

    const layout = el("div", "pe-layout");
    const browser = el("nav", "pe-browser");
    browser.setAttribute("aria-label", "Catalog search results");
    const results = el("div", "pe-results");
    results.id = "pe-results";
    const detail = el("section", "pe-detail");
    detail.setAttribute("aria-label", "Selected Lean declaration or module");
    browser.append(results);
    layout.append(browser, detail);
    root.append(layout);

    const provenance = el("div", "pe-provenance");
    provenance.append(el("p", "", model.publicNodes.length.toLocaleString() + " source-indexed declarations · " + model.auxiliary.length.toLocaleString() + " supplemental nodes · " + model.modules.length.toLocaleString() + " modules"));
    if (model.data.lean_toolchain) provenance.append(el("p", "", "Toolchain: " + model.data.lean_toolchain));
    if (model.data.proof_sources_sha256) {
      const fingerprint = el("p", "", "Proof-source SHA-256: ");
      fingerprint.append(el("code", "", model.data.proof_sources_sha256));
      provenance.append(fingerprint);
    }
    if (typeof model.data.dependency_policy === "string") provenance.append(el("p", "", "Dependency policy: " + model.data.dependency_policy));
    if (typeof model.data.statement_policy === "string") provenance.append(el("p", "", "Statement policy: " + model.data.statement_policy));
    const catalogLink = el("a", "", "Download this catalog (JSON)");
    catalogLink.href = root.dataset.catalogResolved;
    provenance.append(catalogLink);
    root.append(provenance);

    function changeView(view) {
      state.view = view;
      state.limit = PAGE_SIZE;
      renderResults();
    }
    function filteredNodes() {
      const tokens = search.value.trim().toLowerCase().split(/\s+/).filter(Boolean);
      if (state.view === "modules") return model.modules.filter((m) => tokens.every((t) => m.name.toLowerCase().includes(t)));
      const candidates = scope.select.value === "all" ? model.all : scope.select.value === "supplemental" ? model.auxiliary : model.publicNodes;
      return candidates.filter((node) => (!kind.select.value || node.kind === kind.select.value)
        && (!module.select.value || node.module === module.select.value)
        && tokens.every((t) => node.search.includes(t)));
    }
    function renderResults() {
      const isModules = state.view === "modules";
      declarationsButton.setAttribute("aria-pressed", String(!isModules));
      modulesButton.setAttribute("aria-pressed", String(isModules));
      for (const filter of [scope, kind, module]) filter.container.hidden = isModules;
      const matches = filteredNodes();
      const shown = matches.slice(0, state.limit);
      status.textContent = matches.length.toLocaleString() + " " + (isModules ? "modules" : "declarations") + " match · " + shown.length.toLocaleString() + " shown";
      results.replaceChildren();
      if (!matches.length) {
        results.append(el("p", "pe-empty", "No matches. Try a shorter name or reset the filters."));
        return;
      }
      const list = el("ul");
      for (const node of shown) {
        const li = el("li");
        const link = isModules ? moduleLink(node.name, "") : declarationLink(node.name, "", "");
        link.className = "pe-result";
        link.replaceChildren(el("span", "pe-result-name", shortName(node.name)));
        const caption = isModules
          ? (model.byModule.get(node.name) || []).filter((n) => !n.supplemental).length + " source-indexed declarations"
          : (node.kind || "declaration") + (node.supplemental ? " · supplemental" : "") + " · " + (node.module || "module unavailable").replace(/^FreeEntropy\./, "");
        link.append(el("span", "pe-result-meta", caption));
        if (state.selected === (isModules ? "module:" : "declaration:") + node.name) link.setAttribute("aria-current", "true");
        li.append(link); list.append(li);
      }
      results.append(list);
      if (matches.length > shown.length) results.append(button("Show " + Math.min(PAGE_SIZE, matches.length - shown.length) + " more", () => {
        const top = results.scrollTop;
        state.limit += PAGE_SIZE; renderResults(); results.scrollTop = top;
      }, "pe-button pe-more"));
    }
    function refreshSelectionMarker() {
      for (const link of results.querySelectorAll("a.pe-result")) {
        const selectedHash = state.selected ? hrefFor(state.selected.startsWith("module:") ? "module" : "declaration", state.selected.slice(state.selected.indexOf(":") + 1)) : "";
        if (link.getAttribute("href") === selectedHash) link.setAttribute("aria-current", "true");
        else link.removeAttribute("aria-current");
      }
    }
    search.addEventListener("input", () => {
      clearTimeout(state.timer);
      state.timer = setTimeout(() => { state.limit = PAGE_SIZE; renderResults(); }, 120);
    });
    search.addEventListener("keydown", (event) => {
      if (event.key === "Enter") {
        clearTimeout(state.timer); state.limit = PAGE_SIZE; renderResults();
        const first = results.querySelector("a");
        if (first) { state.focusSelection = true; first.click(); }
      }
    });
    for (const filter of [scope, kind, module]) filter.select.addEventListener("change", () => { state.limit = PAGE_SIZE; renderResults(); });

    function focusHeading() {
      if (!state.focusSelection) return;
      state.focusSelection = false;
      const heading = detail.querySelector("h2");
      if (heading) {
        heading.tabIndex = -1;
        heading.focus({ preventScroll: true });
        detail.scrollIntoView({ block: "start" });
      }
    }
    function copyAction(label, content, announcement) {
      return button(label, async () => {
        try {
          if (!navigator.clipboard || !navigator.clipboard.writeText) throw new Error("Clipboard not available");
          await navigator.clipboard.writeText(content);
          announcement.textContent = "Copied.";
        } catch (_) {
          announcement.textContent = "Clipboard unavailable. Select and copy the displayed text or link.";
        }
      });
    }
    function detailsBlock(title) {
      const wrapper = el("details");
      const summary = el("summary", "", title);
      const body = el("div", "pe-details-body");
      wrapper.append(summary, body);
      return { wrapper, body };
    }
    function referenceList(values, external) {
      const container = el("div");
      const list = el("ul", "pe-ref-list");
      let limit = PAGE_SIZE;
      function draw() {
        list.replaceChildren();
        for (const name of values.slice(0, limit)) {
          const item = el("li");
          const target = model.byName.get(name);
          if (!external && target) {
            item.append(declarationLink(name));
            if (target.supplemental) item.append(el("span", "pe-ref-kind", "supplemental"));
          } else {
            item.append(el("code", "", name));
            if (!external) item.append(el("span", "pe-ref-kind", "not expanded in catalog"));
          }
          list.append(item);
        }
        container.replaceChildren(list);
        if (values.length > limit) container.append(button("Show " + Math.min(PAGE_SIZE, values.length - limit) + " more", () => { limit += PAGE_SIZE; draw(); }, "pe-button pe-more"));
      }
      draw();
      if (!values.length) container.append(el("p", "pe-help", "No recorded references in this category."));
      return container;
    }
    function dependencySection(title, values, external) {
      const block = detailsBlock(title + " (" + values.length.toLocaleString() + ")");
      let loaded = false;
      block.wrapper.addEventListener("toggle", () => {
        if (!loaded && block.wrapper.open) {
          loaded = true;
          if (external) block.body.append(el("p", "pe-help", "External names are recorded, but their dependencies are outside this project's graph."));
          block.body.append(referenceList(values, external));
        }
      });
      return block.wrapper;
    }
    function neighbourhood(node) {
      const wrapper = el("div", "pe-neighbourhood");
      const title = el("h3", "", "Direct neighbourhood");
      title.style.marginTop = "0";
      const graph = el("div", "pe-graph");
      const legend = el("p", "pe-graph-legend");
      let limit = 5;
      const expand = button("Expand preview", () => { limit = limit === 5 ? 12 : 5; draw(); });
      function draw() {
        graph.replaceChildren();
        const reverse = model.usedBy.get(node.name) || [];
        for (const [label, values] of [["Used by", reverse], ["Depends on", node.dependencies]]) {
          const column = el("div");
          column.append(el("h4", "", label + " · " + values.length));
          const visible = [...values].sort((a, b) => Number(model.byName.get(a)?.supplemental || false) - Number(model.byName.get(b)?.supplemental || false) || a.localeCompare(b)).slice(0, limit);
          for (const name of visible) {
            const link = model.byName.has(name) ? declarationLink(name, "pe-graph-node") : el("span", "pe-graph-node", shortName(name));
            column.append(link);
          }
          if (!values.length) column.append(el("p", "pe-help", "None recorded"));
          if (values.length > limit) column.append(el("p", "pe-help", "+ " + (values.length - limit) + " in the full list below"));
          graph.append(column);
          if (label === "Used by") graph.append(el("div", "pe-graph-centre", "→ selected declaration →"));
        }
        legend.textContent = "Each edge is one recorded reference. At most " + limit + " neighbours per side; source-indexed nodes appear first. This is not the entire proof graph.";
        expand.textContent = limit === 5 ? "Expand preview (up to 12 per side)" : "Collapse preview";
        expand.hidden = Math.max(reverse.length, node.dependencies.length) <= 5;
      }
      draw();
      wrapper.append(title, graph, legend, expand);
      return wrapper;
    }
    function renderDeclaration(node) {
      state.selected = "declaration:" + node.name;
      detail.replaceChildren();
      const tags = el("div", "pe-tags");
      tags.append(el("span", "pe-tag", node.kind || "declaration"));
      tags.append(el("span", "pe-tag", node.supplemental ? "Supplemental catalog node" : "Source-indexed declaration"));
      detail.append(tags, el("h2", "", node.name));
      const moduleRow = el("p", "pe-help", "Module: ");
      moduleRow.append(model.moduleByName.has(node.module) ? moduleLink(node.module) : el("span", "", node.module || "unavailable"));
      detail.append(moduleRow);
      if (node.supplemental) detail.append(el("p", "pe-help", "This supplemental node preserves an actual dependency step. It is not one of the source-indexed declarations counted on the main list."));
      const actions = el("div", "pe-actions");
      const announcement = el("span", "pe-copy-status");
      announcement.setAttribute("role", "status");
      const share = new URL(location.href);
      share.hash = hrefFor("declaration", node.name).slice(1);
      actions.append(sourceLink(node.file, node.line), copyAction("Copy share link", share.href, announcement), copyAction("Copy Lean name", node.name, announcement), announcement);
      detail.append(actions, el("h3", "", "Pretty-printed kernel type"));
      detail.append(el("p", "pe-help", "The authoritative type comes from the compiled Lean environment. Ordinary notation may hide implicit arguments or display proof arguments as ⋯. This is not the proof term."));
      const code = el("pre", "pe-code");
      code.append(el("code", "language-lean", node.statement));
      code.tabIndex = 0;
      code.setAttribute("aria-label", "Pretty-printed Lean kernel type for " + node.name);
      detail.append(code, copyAction("Copy kernel type", node.statement, announcement));
      if (node.source_statement) {
        const source = detailsBlock("Source header · reading aid");
        source.body.append(el("p", "pe-help", "Surface syntax from the source. The kernel type above determines the checked statement."));
        const sourceCode = el("pre", "pe-code");
        sourceCode.append(el("code", "language-lean", node.source_statement));
        source.body.append(sourceCode);
        detail.append(source.wrapper);
      }
      detail.append(el("h3", "", "Dependencies"), el("p", "pe-help", "Immediate type/body references and inductive, constructor, or recursor structural links. External libraries are listed separately. Used-by edges include supplemental catalog nodes."));
      detail.append(neighbourhood(node));
      detail.append(dependencySection("Depends on · project", node.dependencies, false));
      detail.append(dependencySection("Used by · project", model.usedBy.get(node.name) || [], false));
      detail.append(dependencySection("External references · not expanded", node.external_dependencies, true));
      refreshSelectionMarker(); focusHeading();
    }
    function renderModule(selectedModule) {
      state.selected = "module:" + selectedModule.name;
      detail.replaceChildren(el("span", "pe-tag", "Lean module"), el("h2", "", selectedModule.name));
      const actions = el("div", "pe-actions");
      const announcement = el("span", "pe-copy-status");
      announcement.setAttribute("role", "status");
      const share = new URL(location.href);
      share.hash = hrefFor("module", selectedModule.name).slice(1);
      actions.append(sourceLink(selectedModule.file, null, "Open module on GitHub ↗"), copyAction("Copy share link", share.href, announcement), announcement);
      detail.append(actions);
      const declarations = model.byModule.get(selectedModule.name) || [];
      const indexed = declarations.filter((node) => !node.supplemental);
      const supplemental = declarations.filter((node) => node.supplemental);
      detail.append(el("p", "", indexed.length + " source-indexed declarations and " + supplemental.length + " supplemental nodes."));
      detail.append(button("Browse this module's declarations", () => {
        search.value = ""; scope.select.value = "public"; kind.select.value = "";
        module.select.value = selectedModule.name; changeView("declarations");
        results.querySelector("a")?.focus();
      }));
      detail.append(el("h3", "", "Source-indexed declarations"), referenceList(indexed.map((node) => node.name), false));
      detail.append(dependencySection("Supplemental declarations", supplemental.map((node) => node.name), false));
      detail.append(el("h3", "", "Direct module imports"), el("p", "pe-help", "Imports describe module loading, not which declarations a theorem's proof uses."));
      const imports = el("ul", "pe-ref-list");
      for (const name of names(selectedModule.imports)) {
        const li = el("li");
        li.append(model.moduleByName.has(name) ? moduleLink(name) : el("code", "", name));
        if (!model.moduleByName.has(name)) li.append(el("span", "pe-ref-kind", "outside catalog"));
        imports.append(li);
      }
      detail.append(imports);
      refreshSelectionMarker(); focusHeading();
    }
    function selectFromHash() {
      const raw = location.hash.slice(1);
      const params = new URLSearchParams(raw);
      let declaration = params.get("declaration") || params.get("decl");
      const moduleName = params.get("module");
      if (!declaration && raw && !raw.includes("=")) {
        try {
          const decoded = decodeURIComponent(raw);
          if (model.byName.has(decoded) || decoded.startsWith("FreeEntropy.")) declaration = decoded;
          else if (state.selected) return; // Leave ordinary wiki heading anchors alone.
        } catch (_) { /* Leave malformed non-catalog fragments to the browser. */ }
      }
      if (declaration) {
        if (model.byName.has(declaration)) renderDeclaration(model.byName.get(declaration));
        else renderUnknown("Declaration", declaration);
      } else if (moduleName) {
        if (model.moduleByName.has(moduleName)) renderModule(model.moduleByName.get(moduleName));
        else renderUnknown("Module", moduleName);
      } else {
        const first = (model.data.landmarks || fallback).flatMap((l) => names(l.names)).find((name) => model.byName.has(name));
        if (first) renderDeclaration(model.byName.get(first));
        else detail.replaceChildren(el("h2", "", "Explore the Lean proof"), el("p", "", "Select a declaration or module to inspect its statement and dependencies."));
      }
    }
    function renderUnknown(kindName, name) {
      state.selected = null;
      detail.replaceChildren(el("h2", "", kindName + " not found"), el("p", "", name), el("p", "pe-help", "This link may refer to a different source snapshot. Search the current catalog or choose a main result above."));
      refreshSelectionMarker(); focusHeading();
    }
    ui.selectFromHash = selectFromHash;
    renderResults(); selectFromHash();
  }

  function initialize() {
    const root = document.getElementById("proof-explorer");
    if (active && active.root !== root) {
      clearTimeout(active.state.timer);
      active = null;
    }
    if (!root) return;
    if (controllers.has(root)) {
      active = controllers.get(root);
      active.selectFromHash();
      return;
    }
    if (root.dataset.initialized) return;
    root.dataset.initialized = "true";
    const url = root.dataset.catalogUrl ? new URL(root.dataset.catalogUrl, document.baseURI).href : FALLBACK_CATALOG;
    root.dataset.catalogResolved = url;
    loadCatalog(url).then((model) => {
      if (root.isConnected && document.getElementById("proof-explorer") === root) startExplorer(root, model);
      else delete root.dataset.initialized;
    }).catch((error) => {
      if (!root.isConnected) { delete root.dataset.initialized; return; }
      root.setAttribute("aria-busy", "false");
      const notice = el("div", "pe-error");
      notice.setAttribute("role", "alert");
      notice.append(el("p", "", "The proof catalog could not be loaded."), el("p", "pe-help", error.message));
      notice.append(button("Retry", () => {
        root.replaceChildren(el("p", "pe-loading", "Loading the Lean declaration catalog…"));
        root.setAttribute("aria-busy", "true");
        delete root.dataset.initialized;
        initialize();
      }));
      root.replaceChildren(notice);
    });
  }

  window.addEventListener("hashchange", () => {
    if (active && active.root.isConnected) active.selectFromHash();
  });
  if (document.readyState === "loading") document.addEventListener("DOMContentLoaded", initialize, { once: true });
  else initialize();
  // Material instant navigation replaces the article without reloading scripts.
  if (typeof document$ !== "undefined") document$.subscribe(initialize);
})();
