# Lean formalization and reproduction

The repository includes Lean certificates for the two target theorems in the
bundled `article.tex`: asymptotic quantum memory cost (`thm:qmdl`) and finite
cloning accuracy (`thm:main`). The manuscript labels identify the formalized
statements; theorem numbering in older wiki source snapshots can differ.

The [repository README](https://github.com/JWang226/QMDL#reproduce-the-lean-proof-check)
gives commands to clone and build the proof, audit its axioms, compare the
expected statements with Comparator, and check exported proofs with Nanoda.
The toolchain and dependency revisions are pinned.

Read the [formalization status](https://github.com/JWang226/QMDL/blob/main/docs/FORMALIZATION_STATUS.md)
for the mathematical scope, differences in presentation, and which checks
have actually run. The
[manuscript-to-Lean map](https://github.com/JWang226/QMDL/blob/main/metadata/natural-language-map.json)
connects source labels with the formal declarations. Mechanical checking and
human review of the correspondence are recorded separately.

Related wiki explanations: [[results/achievability|Achievability]],
[[results/converse|Converse]], and [[results/cloning-fidelity|Cloning fidelity]].
