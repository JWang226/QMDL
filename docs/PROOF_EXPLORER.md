# Proof explorer: data generation and scope

The [wiki proof explorer](https://jwang226.github.io/Quantum-Minimum-Description-Length/proof-explorer/) presents
the actual compiled Lean declarations behind the Article's formalization. Its
catalog is generated from the checked project, rather than from an inferred
English proof outline. The separate [verification documentation](https://github.com/JWang226/Quantum-Minimum-Description-Length/blob/main/docs/REPRODUCIBILITY.md)
describes the proof checks; generating or viewing the catalog is not another
proof check.

## Reproduce the catalog

From a checkout with the pinned toolchain, installed dependencies, a completed
`FreeEntropy` build, and a current passing `lean/verification/summary.json`:

```sh
python3 scripts/generate_proof_catalog.py
python3 scripts/generate_proof_catalog.py --check
```

The generator invokes `lake env lean --run scripts/export_proof_catalog.lean`
from the selected Lean project. It reads compiled artifacts without modifying
the proof sources or rebuilding them. To reuse a separate completed build:

```sh
python3 scripts/generate_proof_catalog.py --build-dir /path/to/matching/lean
```

The selected build must have a passing, current audit and the same proof-source
fingerprint, root import file, toolchain and dependency manifest as the source
checkout. The generator refuses a different source snapshot. It can use
`--lake /path/to/lake`; its default searches `PATH`, then `~/.elan/bin/lake`.

`--check` needs only Python 3.9 or later and local source files, not Lean or a
compiled build. It checks the saved catalog's payload checksum, current proof
audit, source and generator fingerprints, inventory, source locations,
dependency partitions, and manuscript landmarks. `--root /path/to/checkout`
selects a different checkout. This mode is suitable for the wiki deployment
job; it detects a stale or accidentally altered catalog. The checksum is not a
signature and does not independently prove that the exporter ran correctly.
For a stronger reproducibility check, regenerate from the matching audited
build and compare the resulting file byte for byte. Generation is deterministic
and records no timestamp or machine-specific path.

## Where the information comes from

- **Statements:** `Lean.ConstantInfo.type`, pretty-printed by the pinned Lean
  version. Generalized parameters and existential binder types are included.
  This is a rendering of the compiled type, not a verbatim source header.
  Ordinary notation can hide implicit arguments and display proof arguments
  as `⋯`; universe parameter names are also recorded separately. The source
  link opens the actual defining module at Lean's declaration location.
- **Immediate references:** constants occurring in that compiled type or
  value, including opaque values. Inductive constructors, a constructor's
  parent inductive, and recursor families/rules supply separately marked
  structural references. Self-edges are omitted. These are syntactic references
  in the compiled environment, not a claim that every reference is a necessary
  mathematical assumption or part of a minimal proof.
- **Project membership:** the defining module recorded by Lean. References to
  Mathlib and Lean are external; their own dependency graphs are not expanded.
  The loaded environment decides declaration identity, including generated
  declarations that occur in more than one imported module's artifact.
- **Source-indexed declarations:** the explicit name list in the existing
  generated `lean/Audit.lean`. Each name must resolve in the loaded kernel
  environment. This list contains the project's public theorems, lemmas,
  definitions and abbreviations; it is not the entire environment.
- **Supplemental declarations:** every other compiled constant defined in a
  project module. These include source-defined structures, private helpers,
  instances, constructors, projections and compiler-generated proof helpers.
  They remain real nodes. A link through a helper is never silently replaced
  by a purported direct link to its dependencies. Some generated nodes have no
  source range and link to their module instead.
- **Module imports:** the compiled `ModuleData.imports`, shown separately.
  Importing a module is not evidence that each of its declarations is used.
- **Landmarks:** existing manuscript labels and fully qualified Lean names in
  `metadata/natural-language-map.json`. These are curated explanatory routes,
  not extra edges added to the compiled reference graph.

“Used by” reverses recorded edges within the indexed project. It does not mean
all uses in Mathlib or other projects. Structural references can form cycles,
so this is a reference graph rather than necessarily a directed acyclic graph.

## Catalog format

`docs/assets/lean-catalog.json` uses version 1 and contains:

| Field | Meaning |
| --- | --- |
| `proof_sources_sha256`, `lean_toolchain`, `mathlib_revision` | Source and environment bindings matching the proof audit. |
| `input_sha256` | Hashes of the exporter, generator, audit seed, root imports, manifest, toolchain and manuscript map. |
| `catalog_sha256` | SHA-256 of canonical JSON with this field removed. |
| `counts` | Source-indexed declarations, proved declarations, proof modules and supplemental declarations. |
| `declarations`, `auxiliary_declarations` | Disjoint arrays of actual declarations. |
| `modules` | Module names, repository-relative source paths and direct imports. |
| `landmarks` | Manuscript-map identifiers, titles and Lean names. |
| `dependency_policy`, `statement_policy` | Human-readable limits displayed in the explorer. |

Each declaration has `name`, `kind`, `module`, `file`, one-based `line` (or
`null` when unavailable), `statement`, `level_parameters`, `dependencies` and
`external_dependencies`. The latter two are sorted, unique name arrays.
`dependency_origins` and `external_dependency_origins` are parallel arrays of
bitmasks: 1 means type, 2 means value, and 4 means structural; bits combine when
a reference has more than one origin. `source_range`, when available, records
Lean's complete source position information. No proof terms are shipped as
executable code; the browser treats catalog strings as text.

The generator validates all project edges against the combined declaration
inventory. The main counts stay comparable with the proof audit even though
the supplemental nodes make the browsing graph larger. The catalog does not
add the Letter's geometric entropy results to the formalization's scope.

## Design reference

The public [Fermat proof browser](https://tianyipeng.github.io/fermats-last-theorem/)
and its [generator documentation](https://github.com/anthropics/fermats-last-theorem/tree/main/tools/docs-site)
inspired the statement/source/landmark navigation. Its own documentation says
that its citation graph is extracted from theorem-module imports. QMDL's
modules hold many declarations, so this exporter instead reads actual compiled
constant references and keeps imports separate. No generator or frontend code
from that project is copied here.
