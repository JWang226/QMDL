# Holevo Information

**Appears in:** [[Article]] (the universal-compression discussion, `sec:redundancy`); [[Letter]] (Discussion); historical [[Notes]] (unitary-programming arguments).

## Definition

For an ensemble $\{p_x,\rho_x\}$, the Holevo quantity is

$$\chi_H=S\!\left(\sum_xp_x\rho_x\right)-\sum_xp_xS(\rho_x),$$

where $S(\rho)=-\operatorname{Tr}(\rho\log\rho)$. It is the mutual information between the classical preparation label and the quantum system. Any measurement's classical information about that label is bounded above by $\chi_H$.

If the ensemble is encoded in a memory of dimension $m$, its Holevo information is at most $\log_2m$. Data processing makes this useful for lower bounds, although a sharp constant-order compression converse requires more than this observation alone.

## Known-Spectrum Universal Coding

Let $\rho_U=U\rho U^\dagger$ and $\bar\rho_n=\int\rho_U^{\otimes n}\,dU$. The Haar ensemble has

$$\chi_H=S(\bar\rho_n)-nS(\rho)
=D(\rho^{\otimes n}\Vert\bar\rho_n).$$

The Article's `prop:orbit_redundancy` identifies this with the exact minimax excess in ideal average code length:

$$R_n(x)=\inf_{\sigma_n}\sup_U
D(\rho_U^{\otimes n}\Vert\sigma_n)
=\sum_\lambda q_{\lambda,n}
\bigl[\log\dim H_\lambda-S(\rho_\lambda)\bigr].$$

The infimum ranges over normalized code states with the required support. An invariant code with a different sector distribution $P_n$ incurs the additional classical penalty $D(q\Vert P_n)$, as stated in `eq:invariant_split`.

For distinct positive eigenvalues, the Article then derives

$$R_n(x)=L_{d,r}(n,x)-s_{\mathrm{blk}}(x)+o(1),$$

where $L_{d,r}$ is the optimal QMDL formula and `eq:block_entropy_limit` defines

$$s_{\mathrm{blk}}(x)=\sum_{1\le i<j\le r}
\left[-\log\left(1-\frac{x_j}{x_i}\right)
-\frac{x_j}{x_i-x_j}\log\frac{x_j}{x_i}\right].$$

The sum is finite for the allowed spectra and is zero for rank one. This entropy correction distinguishes redundancy in ideal average length from the memory-dimension cost of QMDL. The Letter summarizes this result in its Discussion.

## Distinction from the Formalized Converse

The current Lean [[results/converse|compression converse]] transfers a physical source code to an irreducible orbit and applies a quantitative memory bound. It does not infer the constant-order result from a continuity estimate with an uncontrolled error-times-$\log n$ term, or from exact Koashi–Imoto structure alone.

The universal-lossless-coding identities and block-entropy limit above are additional Article results outside the current Lean endpoints. Historical Notes also use Holevo bounds in unitary-programming arguments. Those arguments are not part of the Article's formalized Theorem 1 or Theorem 2, and do not establish the Letter's broader free-entropy programming conjecture. See [[proof-structure]] and [[open-questions/free-entropy-conjecture]].

## Two Different Chi Quantities

The Holevo quantity $\chi_H$ is a von Neumann entropy difference. Voiculescu's [[concepts/free-entropy|free entropy]] $\chi$ measures matrix-microstate volume. The shared symbol does not identify them; this wiki uses the subscript $H$ to distinguish Holevo information.

## Related

- [[concepts/quantum-minimum-description-length|Quantum Minimum Description Length]]
- [[concepts/koashi-imoto|Koashi–Imoto Structure]]
- [[concepts/free-entropy|Free Entropy]]

## References

- A. S. Holevo, "Bounds for the quantity of information transmitted by a quantum communication channel," *Problems of Information Transmission* 9(3), 177–183 (1973).
- `hayashi2010universal`: Universal quantum lossless data compression.
