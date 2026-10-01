# Article: Quantum minimum description of density matrices

**Authors:** Patrick Hayden, Alexander Maloney, Jinzhao Wang, Yuxiang Yang

**Current source:** [repository-root `article.tex`](https://github.com/JWang226/QMDL/blob/main/article.tex)

**Source identity:** the manuscript hash and exact statement labels are recorded in
[the manuscript-to-Lean map](https://github.com/JWang226/QMDL/blob/main/metadata/natural-language-map.json).

The Article proves the optimal quantum memory cost for a known spectrum and
unknown eigenbasis through its additive constant. Its main technical tool
is a finite trace-distance estimate for generalized cloning channels.
See [[proof-structure|Current proof structure]] for the current proof route and [[formalization|Formalization and reproduction]]
for the boundary between the paper and the mechanically checked statements.

## Current theorem index

| Result | Source label | Wiki explanation | Lean endpoint |
| --- | --- | --- | --- |
| Theorem 1: optimal memory cost | `thm:qmdl` | [[results/achievability|Achievability]] and [[results/converse|converse]] | `FreeEntropy.theorem1_achievability` and `FreeEntropy.theorem1_converse` |
| Theorem 2: cloning accuracy | `thm:main` | [[results/cloning-fidelity|Finite cloning accuracy]] | `FreeEntropy.ExteriorRepresentation.theorem2_cloning_accuracy_choi` |
| Separate achievability statement | `thm:achievability` | [[results/achievability|Achievability]] | The achievability part of Theorem 1 |
| Separate converse statement | `thm:converse` | [[results/converse|Converse]] | Haar-average and worst-case versions of Theorem 1 |

Older wiki snapshots called cloning “Theorem 1,” achievability “Theorem 2,”
and converse “Theorem 3.” Those names do not identify the current source.
Use the labels above; numbering in the [[Letter]] and [[Notes]] belongs to
those documents separately.

## Source sections and proof roles

| Section | Label | Role |
| --- | --- | --- |
| Introduction | `sec:intro` | Compression task, exact cost formula and main theorem. |
| Background | `sec:background` | Earlier results and the qubit YCH protocol. |
| Generalized cloning channels | `sec:cloner` | PRV/Choi definition, Cartan formula, reverse channel and finite bound. |
| Achievability | `sec:direct` | Typical sectors, padded target, total encoder/decoder and memory asymptotic. |
| Converse | `sec:converse` | Quantitative irreducible-orbit memory bound and a uniform spectral gap. |
| Universal quantum data compression and QMDL | `sec:redundancy` | Lossless-coding overhead and block entropy; outside the two-theorem formalization. |
| Trace-distance bounds for generalized cloning | `sec:fidelity` | Weight multiplicities, traced projector deficit, mean depth and dimension ratios. |
| Proofs | `app:proofs` | Supporting mathematical proofs. |
| Additional cost of an unknown spectrum | `app:unknown_spectrum` | Additional classical penalty; outside the formalized scope. |

## Relationship to the formal proof

The Lean library supplies the representation, dimension, concentration,
channel and transfer inputs needed by the two main endpoints. It also proves
the connection from constructed Cartan channels to the Article's literal
Choi-projector formulas and the reverse Petz expression. These are not left
as unproved endpoint assumptions.

Some supporting estimates are implemented differently. In particular,
the final formalized converse uses a proved positive uniform spectral-gap
constant sufficient for the limiting lower bound, rather than requiring the
Article's sharper intermediate estimate. See the
[detailed coverage record](https://github.com/JWang226/QMDL/blob/main/docs/FORMALIZATION_STATUS.md)
for these distinctions. No claim is made that every proposition or the later
entropy discussion has been formalized.
