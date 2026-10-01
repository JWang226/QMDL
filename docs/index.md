# Quantum minimum description of density matrices

Lean 4 proofs of Article Theorems 1 and 2, by **Patrick Hayden, Alexander Maloney,
Jinzhao Wang and Yuxiang Yang**. The formalization was developed with assistance
from Codex. The current [Article](https://github.com/JWang226/QMDL/blob/main/article.tex)
and [Letter](https://github.com/JWang226/QMDL/blob/main/letter.tex) are included in
the [repository](https://github.com/JWang226/QMDL).

<div class="qmdl-reading-links">
<a href="proof-structure/"><strong>Read the proof route</strong><span>From representations to optimal memory</span></a>
<a href="proof-explorer/"><strong>Explore the Lean statements</strong><span>Search declarations and follow dependencies</span></a>
<a href="verify/"><strong>Check it yourself</strong><span>Copy commands for Lean, Comparator and Nanoda</span></a>
</div>

## What is proved

A known-spectrum state has an unknown eigenbasis. One pair of quantum channels
must compress and recover its entire $n$-copy state for every basis, with
vanishing global trace-distance error. All retained quantum and classical
registers count toward the memory.

For fixed dimension $d$, rank $r$, and distinct positive eigenvalues
$x_1>\cdots>x_r>0$ summing to one, with all remaining eigenvalues zero, define

$$
L_{d,r}(n,x)=\frac{r(2d-r-1)}2\log_2 n
+\sum_{1\le i<j\le r}\log_2(x_i-x_j)
+(d-r)\sum_{i=1}^r\log_2 x_i
-\sum_{k=d-r}^{d-1}\log_2(k!).
$$

| Result | Conclusion | Exact Lean statement |
| --- | --- | --- |
| Article Theorem 1: achievability | Constructed CPTP codes attain $L_{d,r}(n,x)+o(1)$ memory, with worst-case error $O(\log n/\sqrt n)$. | [theorem1_achievability](proof-explorer.md#declaration=FreeEntropy.theorem1_achievability) |
| Article Theorem 1: converse | Every physical code with vanishing Haar-average error satisfies $\liminf(\log_2\dim M_n-L_{d,r}(n,x))\ge0$. The worst-case criterion is also covered. | [theorem1_converse](proof-explorer.md#declaration=FreeEntropy.theorem1_converse) |
| Article Theorem 2: cloning | Both original Choi-projector channels have trace error at most $C_{d,x}\|\nu-\mu\|_1/(b_\mu+1)$. | [theorem2_cloning_accuracy_choi](proof-explorer.md#declaration=FreeEntropy.ExteriorRepresentation.theorem2_cloning_accuracy_choi) |

Theorem 1 includes every positive rank and $d=1$. Theorem 2 requires $d\ge2$,
partitions supported on the first $r$ rows, and a dominant integral difference,
which may have negative entries. Its channels, representations, dimensions,
concentration and covariance facts are constructed or proved in the library.
The [[intro|introduction]] explains these statements; the [[proof-structure|proof route]]
connects each step to its Lean module.

## Verification

The recorded local check covers **270 proof modules**, **1,873 proved declarations**
and **2,499 public declarations**. The proof library has no unresolved placeholders
or custom axioms. Its transitive axiom audit permits only `propext`,
`Classical.choice` and `Quot.sound`.

| Check | Recorded result | What it checks |
| --- | --- | --- |
| Lean build and axiom audit | Passed locally | Types, proof terms and transitive axioms of every indexed public declaration. |
| Local Comparator diagnostic | Passed for three configurations / four endpoints | Expected statements and referenced definitions, allowed axioms, and Lean kernel replay. |
| Nanoda, a separate Rust kernel | Passed for all three solution exports | The exported endpoint dependency closures, including required theorem roots. |

The latter two checks were unsandboxed. Independent human review and a
Linux-sandboxed Comparator run are not established. The [[formalization|scope and evidence]]
page identifies the actual records; [[verify|fresh verification]] checks your checkout.

With the prerequisites listed in the verification guide installed:

```sh
git clone https://github.com/JWang226/QMDL.git
cd QMDL
bash scripts/verify.sh all
```

Success ends with `VERIFICATION PASSED: all`. Each invocation saves fresh logs
under `.verify-work/`; a failed command returns a nonzero exit status.
[Separate checker commands and expected verdicts](verify.md) are also documented.

## What remains outside this formalization

The current Letter expresses the optimal memory as
$\tfrac12\chi_{\mathrm{phy}}(\rho;n^{-1})+C_{d,r}+o(1)$ using an ambient
Hilbert–Schmidt tube-volume convention. The Article certificates prove its
memory formula. The Letter's geometric volume calculation, offset identity
and conditional large-dimension bridge have no separate Lean certificates.
Repeated **positive** eigenvalues and broader programming extensions are
outside these endpoints; repeated zeros are already covered.

See [[Letter|the Letter]], [[formalization|the full scope]], and the
[manuscript-to-Lean map](https://github.com/JWang226/QMDL/blob/main/metadata/natural-language-map.json).
The [[wiki-index|mathematical wiki index]] collects the background definitions,
lemmas, references and open questions. English explanations are reading aids;
the exact Lean statements are what the checkers prove.
