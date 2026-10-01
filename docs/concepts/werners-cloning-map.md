# Werner's Cloning Map

**Source:** current [[Article]], `eq:werner` and `eq:qubitcloning` in the YCH review; historical [[Notes]] background.

## The Channel

Werner's cloner maps $n$ identical pure-state copies to an approximate $m$-copy output, $m\ge n$. It exists in every dimension $d$; its qubit instance is used in the [[concepts/ych-scheme|YCH protocol]]. Generalized cloning extends the symmetric-power construction to other highest weights.

Write $d_k=\dim\operatorname{Sym}^k(\mathbb C^d)=\binom{k+d-1}{d-1}$. Let

$$V:\operatorname{Sym}^m(\mathbb C^d)\longrightarrow
\operatorname{Sym}^n(\mathbb C^d)\otimes\operatorname{Sym}^{m-n}(\mathbb C^d)$$

be the intertwining isometry. The Article's intrinsic formula is

$$\mathcal C_{n\to m}(X)=\frac{d_n}{d_m}V^\dagger(X\otimes I_{m-n})V,$$

where $I_{m-n}$ is the identity on the auxiliary symmetric subspace. Equivalently one may write the projected operator in the ambient tensor product. For qubits, $d_k=k+1$ and the prefactor is $(n+1)/(m+1)$.

The map is CPTP and covariant under the same unknown unitary on every copy. For $m=n$ it is the identity; partial trace supplies the reverse direction when reducing the number of copies.

## Global Overlap and Fidelity Convention

For a normalized pure state $\psi$, put

$$\sigma_m=\mathcal C_{n\to m}(|\psi\rangle\langle\psi|^{\otimes n}).$$

The pure target lies in the symmetric subspace, so the formula gives the **global overlap**

$$\langle\psi^{\otimes m}|\sigma_m|\psi^{\otimes m}\rangle=\frac{d_n}{d_m}.$$

Using the wiki's [[notation|unsquared fidelity]] convention,

$$F(\sigma_m,|\psi\rangle\langle\psi|^{\otimes m})
=\left\|\sqrt{\sigma_m}\sqrt{|\psi\rangle\langle\psi|^{\otimes m}}\right\|_1
=\sqrt{\frac{d_n}{d_m}}.$$

Thus for qubits the ratio $(n+1)/(m+1)$ is **squared fidelity**, while the unsquared $F$ is its square root. This is a global $m$-copy figure of merit, distinct from the fidelity of a single output clone. Werner's global optimal-cloning result and Keyl–Werner's single-clone analysis concern these different criteria.

## Role in the Project

The YCH protocol uses this channel between spin sectors: as $\mathrm{SU}(2)$ representations, $\mathcal H_J\simeq\operatorname{Sym}^{2J}(\mathbb C^2)$, and determinant phases cancel under conjugation. The current [[results/cloning-fidelity|Article Theorem 2]] generalizes the needed approximation estimate to supported highest rows, directly in trace distance.

The global pure-state overlap formula above is background; it is not the fidelity convention or an additional optimality assertion supplied by the final mixed-state cloning endpoint.

## Related

- [[concepts/generalized-cloning-map|Generalized Cloning Map]]
- [[concepts/ych-scheme|YCH Scheme]]
- [[open-questions/cloning-optimality|What general cloning optimality would require]]

## References

- [Werner, “Optimal cloning of pure states” (1998)](https://doi.org/10.1103/PhysRevA.58.1827)
- [Keyl and Werner, “Optimal cloning of pure states, judging single clones” (1999)](https://doi.org/10.1063/1.532887)
