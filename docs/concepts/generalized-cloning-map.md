# Generalized Cloning Map

**Appears in:** [[Article]], `eq:gen_cloner`, `prop:choi`, `thm:main`; [[Letter]].

## Intuition

A covariant cloner moves a normalized representation state from $H_\mu$ to $H_\nu$ without knowing its eigenbasis. The Article defines a channel using the distinguished PRV component. For the pairs needed in compression, an actual Cartan embedding gives a concrete formula and a finite error bound.

Covariance alone does not select a unique channel. The additional choice of the multiplicity-one PRV component selects this channel; accuracy and optimality are separate questions.

## Definition and the Cartan Case

The Article's general definition uses $\omega=(\nu-\mu)^+$ and the projector $\Pi_\omega$ in $H_{\mu^*}\otimes H_\nu$:

$$J_\omega=\frac{d_\mu}{d_\omega}\Pi_\omega,\qquad
\mathcal C_{\mu\to\nu}(X)=\operatorname{Tr}_{\mu^*}
\left[J_\omega(X^\top\otimes I_\nu)\right].$$

In the Cartan case, $\omega=\nu-\mu$ is already dominant and $\nu=\mu+\omega$. Let $V:H_\nu\hookrightarrow H_\mu\otimes H_\omega$ be the isometric Cartan intertwiner. Then

$$\mathcal C_{\mu\to\nu}(X)=\frac{d_\mu}{d_\nu}V^\dagger(X\otimes I_\omega)V,
\qquad
\mathcal C_{\nu\to\mu}(Y)=\operatorname{Tr}_\omega(VYV^\dagger).$$

This is the setting constructed in Lean. The auxiliary highest weight can be signed: for example, $(1,-1)$ is dominant. The source and target remain polynomial representations, so their states are defined even at singular density matrices. When $r<d$ and both rows vanish beyond $r$, dominance forces the auxiliary difference to be nonnegative. See [[definitions/generalized-cloning-map-def]].

## Choi Multiplicity and Covariance

For a general decomposition $H_{\mu^*}\otimes H_\nu\simeq\bigoplus_\lambda H_\lambda\otimes\mathbb C^{m_\lambda}$, a covariant Choi operator has form

$$J\simeq\bigoplus_\lambda I_{H_\lambda}\otimes A_\lambda,\qquad A_\lambda\ge0,$$

with trace-preservation constraints. Scalar mixtures of whole-isotypic projectors are not the general form when multiplicities exceed one.

For the chosen multiplicity-one component, Schur's lemma and trace normalization give $\operatorname{Tr}_\nu\Pi_\omega=(d_\omega/d_\mu)I$, so the normalized Choi operator defines a CPTP channel. Minimality in dominance order does not mean smallest dimension or prove optimal fidelity; the Article's example $(\mu,\nu)=((1,0,0),(5,1,0))$ distinguishes those notions.

## Accuracy: Article Theorem 2

For $d\ge2$, a fixed rank-$r$ spectrum with strictly decreasing positive eigenvalues, supported source/target partitions, and dominant signed difference, put

$$D=\|\nu-\mu\|_1,\qquad b_\mu=\min_{1\le i\le\min(r,d-1)}(\mu_i-\mu_{i+1}).$$

Both directions satisfy

$$\frac12\|\mathcal C_{\mu\to\nu}(\rho_\mu)-\rho_\nu\|_1,
\quad\frac12\|\mathcal C_{\nu\to\mu}(\rho_\nu)-\rho_\mu\|_1
\le C_{d,x}\frac{D}{b_\mu+1}.$$

The same maps work for every unitary conjugate. The theorem includes rank one and $\mu=\nu$; in the latter case the Cartan formulas themselves are identity channels. Typical rows give error $O(\log n/\sqrt n)$ in the physical compression protocol.

The reverse map is the Petz recovery map at maximally mixed input. This identity does not assert universal recovery optimality.

## Formal Proof Status

`CanonicalCartanCovariance` proves actual group covariance, including signed auxiliary weights. `CanonicalChoi`, `CanonicalReverseChoi`, `ReverseChoiRepresentation`, and `ReverseChoiMultiplicity` identify both Choi projectors, their highest weights, and the relevant multiplicity-one copies. `theorem2_cloning_accuracy_choi` in `Theorem2Choi.lean` proves the bound for the literal projector-contraction formulas, and `prv_maps_are_channels` proves they are CPTP.

These are actual canonical representation states and maps, not arbitrary matrices satisfying assumed representation or block-estimate axioms. General PRV construction for every nondominant difference is outside the endpoint's scope. The physical protocol uses explicit replacement channels for atypical pairs. See [[proof-structure]].

## Related

- [[results/cloning-fidelity|Cloning Accuracy (Article Theorem 2)]]
- [[concepts/prv-component|PRV Component]]
- [[concepts/casimir-operator|Casimir Trace Deficit]]
- [[concepts/petz-recovery-map|Petz Recovery Map]]
- [[concepts/werners-cloning-map|Werner's Cloning Map]]
- [[open-questions/cloning-optimality|Cloning Optimality]]
