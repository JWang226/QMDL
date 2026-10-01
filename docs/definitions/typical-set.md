# Typical Set of Young Diagrams

**Source:** [[Article]], `eq:typical_set`, `eq:target_rep`, `eq:tail_prob_bound`.

## Statement

Let $x_1>\cdots>x_r>0$, with $x_i=0$ for $i>r$. All logarithms below are base two. Set

$$\epsilon_n=\sqrt{n/2}\log n,\qquad
\mathcal T_{x,n}=\left\{\lambda\vdash n:\ell(\lambda)\le r,\
\max_{1\le i\le r}|\lambda_i-nx_i|\le\epsilon_n\right\}.$$

This is a coordinatewise window in the **unnormalized** row lengths. Its normalized width is $\epsilon_n/n=(\log n)/\sqrt{2n}\to0$.

## Padded Target

Put $\xi_n=2\epsilon_n+1$. The fixed target is

$$\Lambda_i=\begin{cases}
\lceil nx_i+(r-i+1)\xi_n\rceil,&1\le i\le r,\\
0,&i>r.
\end{cases}$$

The $+1$ in $r-i+1$ pads the last positive row as well. For every typical $\lambda$, $\Lambda-\lambda$ is nonnegative and dominant. Adjacent typical rows can fluctuate in opposite directions by a total $2\epsilon_n$; the buffer absorbs this and the ceiling error. The target need not be a partition of $n$.

For example, at $d=r=2$, $n=10000$, and $x=(0.7,0.3)$, $\epsilon_n\approx939.6$ and $\xi_n\approx1880.2$. The target is approximately $(10761,4881)$, with the exact entries given by the ceiling formula. Finite-size padding can be substantial even though it is $o(n)$ asymptotically.

## Concentration and the Formal Proof

The Article displays the supported Schur tail bound

$$\sum_{\lambda\notin\mathcal T_{x,n}}q_{\lambda,n}
\le(n+1)^{r(r+1)/2}\exp[-(\log n)^2/4].$$

The final Lean proof derives concentration directly for the probabilities of the constructed physical irreducible blocks. It uses the proved, coarser prefactor

$$\operatorname{physicalAtypicalMass}(s,n)
\le(n+1)^{(d-1)\binom d2+d}\exp[-(\log_2 n)^2/4],\qquad n\ge2.$$

`physicalAtypicalMass_eventually_le_inv` in `SchurWeylConcentration.lean` then gives a bound of $1/n$ eventually. The pointwise probability bound, decomposition, and multiplicity estimate are proved in the dependency chain; none is a premise of this endpoint. The sharper displayed prefactor from the Article is not claimed by this particular theorem.

## Role in the Protocol

On typical sectors, Theorem 2 gives forward and reverse error $O(\log n/\sqrt n)$. The two atypical contributions add at most twice their probability mass. Replacement channels make the physical encoder and decoder valid on all sectors and for every $n$.

The current converse transfers an arbitrary physical code to the fixed target orbit and applies a quantitative orbit-memory bound. It does not require selecting a good typical sector by Markov's inequality. See [[proof-structure]].

## Used By

- [[results/achievability|Achievability (Article Theorem 1)]]
- [[results/converse|Converse (Article Theorem 1)]]
- [[concepts/schur-weyl-duality|Schur-Weyl Decomposition]]
