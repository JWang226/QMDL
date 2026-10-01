# Formalization status and scope

The Lean development proves the requested conclusions of manuscript Theorems 1 and 2 for actual finite complex matrices and completely positive trace-preserving channels. It does **not** claim to formalize the entire manuscript. The source manuscript is [article.tex](../article.tex); the primary statement locators are its TeX labels, not theorem numbering alone.

## Main results

| Manuscript statement | Lean declaration | Source |
| --- | --- | --- |
| Theorem 1, achievability (`thm:qmdl`, `thm:achievability`) | `FreeEntropy.theorem1_achievability` | [Theorem1Complete.lean](../lean/FreeEntropy/Theorem1Complete.lean) |
| Theorem 1, Haar-average converse (`thm:qmdl`, `thm:converse`) | `FreeEntropy.theorem1_converse` | [Theorem1Complete.lean](../lean/FreeEntropy/Theorem1Complete.lean) |
| Theorem 1, worst-case converse | `FreeEntropy.theorem1_converse_of_uniform` | [Theorem1Complete.lean](../lean/FreeEntropy/Theorem1Complete.lean) |
| Theorem 2, original Choi-projector formulas (`thm:main`) | `FreeEntropy.ExteriorRepresentation.theorem2_cloning_accuracy_choi` | [Theorem2Choi.lean](../lean/FreeEntropy/Theorem2Choi.lean) |
| Theorem 2, equivalent Cartan formulas | `FreeEntropy.ExteriorRepresentation.theorem2_cartan_cloning_accuracy` | [Theorem2Canonical.lean](../lean/FreeEntropy/Theorem2Canonical.lean) |
| Theorem 2, literal Petz recovery expression | `FreeEntropy.ExteriorRepresentation.theorem2_cloning_accuracy_petz` | [Theorem2Petz.lean](../lean/FreeEntropy/Theorem2Petz.lean) |

The [machine-readable mapping](../metadata/natural-language-map.json) locates these statements, their definitions and principal supporting lemmas by TeX label, fully qualified Lean declaration, file and one-based line number. Labels and declaration names are authoritative; line numbers are navigation hints that may change after edits.

## What the endpoints mean

Theorem 1 fixes a normalized spectrum with distinct positive eigenvalues and permits zero eigenvalues. The source is the literal tensor power of `U diag(x) U†`, with `U` ranging over the actual unitary group. Constructed encoders and decoders do not depend on `U`. Memory cost is the base-two logarithm of the dimension of the entire retained register. Achievability includes the manuscript's additive constant and a worst-case error of order `log(n)/sqrt(n)`. The converse applies to arbitrary physical CPTP codes with vanishing normalized-Haar average error. All positive ranks and dimensions, including dimension one, are covered.

Theorem 2 uses supported antitone natural rows and a dominant integral difference, which can have negative entries. It proves both original normalized Choi-projector error bounds for every unitary eigenbasis. The exact row L1 difference and minimum supported adjacent gap are computed in Lean. Rank one and coincident rows are included. Its explicit admissible constant is

`choose(d,2) + 3*N*q/(1-q)^(N+1)`, where `N=choose(r,2)`.

The final theorem endpoints do not take representation existence, decomposition, dimension formulas, multiplicity bounds, spectral normalization, covariance, concentration, local cloning errors or source-transfer estimates as unproved premises. These are constructed or proved in their dependencies. Earlier conditional reductions remain useful intermediate lemmas; their hypotheses should not be confused with those of the final endpoints.

## Fidelity and boundaries

The current companion [Letter](../letter.tex) is bundled with
[its figure](../compression.pdf) and the shared bibliography. The
[companion source map](../metadata/letter-source-map.json) records exact
source hashes and relates its labeled equations to the Article declarations.
The Letter's known-spectrum QMDL formulas (`eq:result_qmdl`,
`eq:rank_def_qmdl`) specialize Theorem 1. Its physical tube-volume definition
and expansions, the explicit half-entropy offset at resolution `n^-1`, and
the conditional large-dimension bridge (`rem:bridge`) have no separate Lean
certificates. Arbitrary repeated positive eigenvalues remain outside the
memory endpoints even though the Letter derives their geometric entropy.

The formalization uses a diagonal reference state and all unitary conjugations to represent the known-spectrum family. Matrix carriers and row indices are explicit and zero-based. The converse uses an extended-real `liminf`. These choices encode the manuscript's conclusions.

The proof is not a line-by-line transcription. For example, the physical concentration proof uses its own polynomial prefactor; the final canonical converse uses the positive uniform gap `(1-q)^(choose(d,2)+1)` rather than requiring the manuscript's sharper intermediate constant. The padded target's precise dimension asymptotic is proved. Explicit replacement channels handle atypical sectors. These choices suffice for the stated theorem conclusions.

The Choi, Cartan and Petz identifications are proved for the actual canonical pairs needed by Theorem 2. This does not assert a construction of the generalized PRV channel for every arbitrary pair of dominant integral weights. The later universal-coding redundancy, block-entropy and unknown-spectrum discussion is outside the requested scope. The mapping also distinguishes exact auxiliary statements from supporting bounds or specializations.

## Verification and review

The clean source rebuild passed for **270 proof modules**, **1,873 proved declarations** and **2,499 public declarations audited**. The proof development has no unresolved `sorry`/`admit` placeholders and no project-specific axioms. Its audited dependencies use only `propext`, `Classical.choice` and `Quot.sound`, the standard Lean axioms allowed by the project.

The rebuild used fresh checkouts of the locked public dependencies, the public Mathlib cache, and no pre-existing project proof artifacts or local package symlinks. All three reader entrypoints also built successfully. See the portable [reproducibility record](../lean/verification/reproducibility.json) and [audit summary](../lean/verification/summary.json). This was a local clean build; a hosted GitHub Actions run is not claimed.

Those counts describe a particular audited source fingerprint. Source edits can change that fingerprint and the counts. Running `lean/check.sh` rebuilds and regenerates the local evidence. The source archive includes the current portable summary and reproducibility record; large raw logs are retained locally and generated afresh by CI.

The project is **agent-reviewed**. Agents checked the mathematical interpretation of the endpoints as well as Lean compilation and the axiom dependencies. Independent human peer review and manuscript-author endorsement have not been established and are not claimed. Kernel checking verifies the formal statements; it does not by itself certify the choice of those statements as a faithful interpretation of prose.

The additional Comparator entrypoints are:

- [Theorem1Achievability.json](../lean/ComparatorChallenges/Theorem1Achievability.json)
- [Theorem1Converse.json](../lean/ComparatorChallenges/Theorem1Converse.json), covering both converse variants
- [Theorem2Choi.json](../lean/ComparatorChallenges/Theorem2Choi.json)

All three configurations passed the local diagnostic: the pinned Comparator accepted the exact exported theorem statements and their referenced definitions, its axiom checker accepted the solution dependencies, and Lean's kernel accepted replay of the exported proofs. This covers achievability, both converse variants, and the Choi cloning result. The run used the clean isolated build and was **unsandboxed** on macOS. All three solution exports also passed independent kernel checking with pinned Nanoda 0.4.19 (Rust 1.90.0), allowing only the same three standard axioms and treating unpermitted axioms as hard errors. This Nanoda run was also unsandboxed; its [execution record](../lean/ComparatorConfig/nanoda-status.json) binds the source and export hashes. A Linux-sandboxed Comparator run has not occurred.

Comparator challenge modules deliberately contain expected-statement proof holes. Those are specification fixtures, not unresolved proofs in `lean/FreeEntropy/`, and are kept outside the production proof audit. Consult the [execution report](../lean/ComparatorChallenges/verification-status.json) for the checked source fingerprints and the [challenge documentation](../lean/ComparatorChallenges/README.md) for the imported definitions that form the trusted statement boundary.

## Dependencies and provenance

The source requires the Lean toolchain and mathlib revision pinned in [lean-toolchain](../lean/lean-toolchain), [lakefile.toml](../lean/lakefile.toml) and [lake-manifest.json](../lean/lake-manifest.json). There are no missing local proof imports or imports of another private project. Any local `.lake/packages` symlinks are replaceable dependency caches, not proof sources required from another repository. Source provenance comments in `Channels.lean` and `CartanChannel.lean` credit adapted algebra from the previously available local Cloning development. [NOTICE](../NOTICE) identifies the affected files. The earlier source was identified privately and matched against the adaptation record; a publicly accessible upstream reference and the licensing record remain incomplete.

The implementation and agent review used Codex with GPT-6-family agents. The exact deployed model version, reliable elapsed work time, token count and monetary cost are unknown; no estimates are presented as measured facts. Software is collectively credited to **Free Entropy formalization contributors**. Manuscript authorship is separately listed in [formalization.yaml](../formalization.yaml). See [AI_PROVENANCE.md](AI_PROVENANCE.md) for the provenance record. License selection and individual attribution are pending maintainer confirmation; this status document does not grant a license.

The root metadata follows the [v0.3 formalization.yaml schema](https://github.com/mathlib-initiative/formalization.yaml/blob/main/schema/v0.3.schema.json), using the [OpenAI ten-proofs metadata](https://github.com/openai/ten-proofs/blob/main/formalization.yaml) as a format example. No affiliation, review claim, authorship or license from that example is transferred to this project.
