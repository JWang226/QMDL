# Schumacher Compression

**Appears in:** [[Letter]] (`eq:vN`, `fig:compression`, and Compression); [[Article]] (Introduction).

## The Compression Criterion

Schumacher compression preserves the source state together with its correlations with a reference system. For a known i.i.d. source $\rho^{\otimes n}$, its leading memory cost is $nS(\rho)$ qubits, where $S(\rho)=-\operatorname{Tr}(\rho\log_2\rho)$.

The project's QMDL task uses a different family and error criterion. Only the spectrum is known to the encoder and decoder, and the reconstructed $n$-copy state must approximate every unknown eigenbasis in global trace distance. No reference system is included in that error.

| | Schumacher compression | Known-spectrum QMDL |
|---|---|---|
| Recovery criterion | Preserve a purification | Recover the $n$-copy orbit state |
| Leading memory cost | $nS(\rho)$ | $\tfrac12r(2d-r-1)\log n$ for distinct positive eigenvalues |
| Source knowledge in the comparison | The state is known | The spectrum is known; the eigenbasis is unknown |
| Entropy relation | von Neumann entropy | Physical free entropy at resolution $n^{-1}$, with an explicit offset |

There are also universal versions of Schumacher compression for unknown sources; the distinction in recovery criteria remains.

## Typical Subspaces

The Letter's `eq:vN` gives the entropy as

$$S(\rho)=\inf_{0<\varepsilon<1}\limsup_{N\to\infty}\frac1N
\min_{\substack{V\subseteq H^{\otimes N}\\
\operatorname{Tr}(\rho^{\otimes N}\Pi_V)\ge1-\varepsilon}}
\log\dim V.$$

At finite $N$, a smallest admissible subspace can be chosen by taking the most likely product eigenvectors until their total probability reaches $1-\varepsilon$. The subspace obtained from an empirical typical set has the same asymptotic rate but need not achieve this finite-$N$ minimum. A typical subspace need not be a tensor product of single-copy subspaces.

## Unknown Pure States

For a known pure state, Schumacher compression is trivial: the decoder can prepare the state, and its entropy is zero. When the pure state is unknown, its $n$ copies can instead be stored exactly in the symmetric subspace, of dimension

$$\binom{n+d-1}{d-1}.$$

The Article's optimal asymptotic memory cost is therefore

$$|M_n|=(d-1)\log n-\log(d-1)!+o(1).$$

For pure states there is no nontrivial purification to preserve; the difference between these two tasks is the encoder's and decoder's source knowledge. This example is included in the Lean theorem.

## Why a Quantum Description Is Retained

The orbit has a local distinguishability scale of order $n^{-1/2}$, which helps explain the logarithmic memory scale. It does not turn the protocol into classical estimation followed by preparation. The Letter stresses that such a procedure cannot make the global $n$-copy error vanish. The actual compression protocol retains a quantum representation register.

The Letter compares two microstate viewpoints: high-probability subspaces lead to von Neumann entropy, while moment-constrained matrix volumes lead to Voiculescu's free entropy. The finite-dimensional physical free entropy then gives a geometric interpretation of the QMDL formula. There is no assumption that a matrix's eigenvalues and eigenvectors are freely independent. See [[concepts/free-probability-theory]] and [[concepts/quantum-minimum-description-length]].

## Formal Scope

The Article's known-spectrum QMDL construction and converse are Lean verified, including the pure-state case. This project does not separately formalize Schumacher's theorem or the Letter's geometric volume calculation. See [[proof-structure]].

## Related

- [[concepts/quantum-minimum-description-length|Quantum Minimum Description Length]]
- [[concepts/free-entropy|Free Entropy]]
- [[concepts/physical-free-entropy|Physical Free Entropy]]

## References

- `schumacher1995quantum`: Schumacher, "Quantum coding" (1995).
- `jozsa1998universal`: Universal quantum compression.
- `hayashi2002quantum`, `hayashi2002simple`, `hayashi2010universal`: Universal coding results cited in the Letter.
