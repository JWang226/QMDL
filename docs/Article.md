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
Use the labels above. The current [[Letter]] presents its central results as labeled equations, not numbered theorem environments; numbering in the historical [[Notes]] belongs to that document separately.

## Correspondence with the Current Letter

The attached Article is byte-identical to the repository's checked `article.tex` (SHA-256 `09fc0a6bb205180cd820be94d843a1dc0d4342a543492e30dde54e367ae843a9`). Refreshing the Letter and wiki does not change the Lean theorem source or the manuscript used for its statement mapping.

| Article result | Current Letter reference | Distinction |
| --- | --- | --- |
| Theorem 1, `thm:qmdl` and `eq:result` | `eq:result_qmdl` for full rank; `eq:rank_def_qmdl` for distinct positive eigenvalues at lower rank | Same optimal memory expansion and converse; the Letter refers to the companion Article for the code and proof. |
| Explicit spectrum-dependent memory constant | `eq:result`, `eq:result_const`, and the rank-deficient End Matter | The Letter combines the memory theorem with a separate tube-volume calculation to express it as one-half physical free entropy plus $C_{d,r}$. |
| Theorem 2, `thm:main` | Compression discussion of typical blocks and a single target irrep | The full finite channel bound is in the Article, not a separately numbered Letter theorem. |
| Unknown-spectrum and lossless-coding discussions | Closing discussion | Extensions have their own hypotheses; they are outside the two-theorem Lean scope. |

The label `eq:result` is reused across documents: it denotes the explicit memory formula in the Article and the free-entropy relation in the Letter. Always include the document when citing it.

The current Letter also derives physical entropy for arbitrary multiplicities and a conditional large-dimension bridge to Voiculescu's entropy. These are additional manuscript results, not consequences already certified by the Article's Lean audit. QMDL for repeated **positive** eigenvalues remains an expected extension; rank deficiency with distinct positive eigenvalues is already included in Article Theorem 1.

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

## Memory Cost Versus Lossless-Coding Overhead

The later section `sec:redundancy` concerns a different operational quantity: the minimax excess **ideal average code length** above $nS(\rho)$. Proposition `prop:orbit_redundancy` identifies the exact code state as the Haar-averaged source. For the distinct-positive-spectrum family, the section obtains

$$R_n(x)=L_{d,r}(n,x)-s_{\mathrm{blk}}(x)+o(1),$$

where `lem:block_entropy` gives the finite nonnegative typical-block entropy $s_{\mathrm{blk}}(x)$ explicitly. Thus this overhead and the QMDL memory cost have the same leading term but can differ at order one. The Letter's closing lossless-coding discussion refers to this result. Neither the redundancy proposition nor its entropy limit is part of the two-theorem Lean claim.

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
