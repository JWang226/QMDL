# Lean proof explorer

Browse the checked declarations behind [[Article|Article Theorems 1 and 2]].
Start from a main result, search a Lean name, or explore a module. The
[[proof-structure|proof structure guide]] explains the mathematical route;
this explorer shows the actual declarations and their recorded dependencies.

The **pretty-printed kernel type** comes from the authoritative compiled Lean
statement. It can expose elaborated parameters, while ordinary Lean notation
can still hide implicit arguments or show proof arguments as `⋯`. It is not
an editorial paraphrase or a verbatim source quotation. The optional source
header is a reading aid.
These statements concern the Article's formalized results; they do not extend
verification to the Letter's geometric entropy calculations.

<div id="proof-explorer" class="proof-explorer" data-catalog-url="../assets/lean-catalog.json" aria-busy="true">
  <span id="declaration=FreeEntropy.theorem1_achievability" hidden></span>
  <span id="declaration=FreeEntropy.theorem1_converse" hidden></span>
  <span id="declaration=FreeEntropy.theorem1_converse_of_uniform" hidden></span>
  <span id="declaration=FreeEntropy.ExteriorRepresentation.theorem2_cloning_accuracy_choi" hidden></span>
  <p class="pe-loading" role="status">Loading the Lean declaration catalog…</p>
</div>

<noscript>This explorer needs JavaScript. Read the <a href="../proof-structure/">proof structure guide</a> or browse the <a href="https://github.com/JWang226/Quantum-Minimum-Description-Length/tree/main/lean/FreeEntropy">Lean sources on GitHub</a>.</noscript>

## What the links mean

**Depends on** lists immediate project references recorded in a declaration's
kernel type and body, plus structural links for inductives, constructors, and
recursors. **Used by** reverses those same edges across the catalog.
Supplemental nodes retain structures, constructors, projections, and other
auxiliary declarations, so those steps are not silently replaced by transitive
links. They are distinct from the source-indexed declarations shown by default.

External references, including Mathlib and Lean, are listed separately; their
own dependency graphs are not expanded here. A module's import list is a
different relation from a declaration's dependencies. The bounded neighbourhood
view is only a preview; the dependency lists retain all recorded edges.

The catalog is an inspection tool, not a new proof checker. See
[[formalization|verification and reproduction]] for Lean, Comparator, Nanoda,
the axiom boundary, and the current verification records. The catalog's source
fingerprint and toolchain are shown below the explorer.
