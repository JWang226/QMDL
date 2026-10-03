# Beyond the Proved State-Compression Relation

**Source:** current [[Letter]], discussion after `eq:result`, `rem:bridge`, and the final paragraph of the End Matter in [letter.tex](https://github.com/JWang226/Quantum-Minimum-Description-Length/blob/main/letter.tex). The earlier [[Notes]] contain additional programming proposals.
**Status:** State compression with distinct positive eigenvalues is established; broader programming and repeated-positive-spectrum extensions remain conjectural.

## What the Current Letter Establishes

For a fixed rank-$r$ spectrum with distinct positive eigenvalues, the [[Article]] proves an attaining code sequence and a matching converse through the additive memory constant. The Letter combines that memory formula with its physical tube-volume calculation to obtain

$$|M_n|=\tfrac12\chi_{\mathrm{phy}}(\rho;n^{-1})+C_{d,r}+o(1).$$

The offset is explicit and depends only on $d$ and $r$. The relation includes rank-deficient states and pure states. It describes the attaining sequence, with a corresponding asymptotic lower bound for arbitrary vanishing-error codes; it is not an equality for every code or every prescribed error schedule.

The current Letter does **not** state numbered QMDL or free-entropy theorems. Its main references are `eq:result_qmdl`, `eq:result`, and `eq:rank_def_qmdl`.

## What Is Still Conjectural

### Repeated Positive Eigenvalues

The Letter derives physical free entropy for arbitrary spectral multiplicities, but its final paragraph only **expects** the corresponding general QMDL relation. Distinct positive eigenvalues plus repeated zeros are already covered. Collisions among positive eigenvalues are the additional case; see [[open-questions/degenerate-spectrum|the degeneracy page]].

### Programming More General Operators

Within settings where free entropy is defined, the Letter conjectures an analogous role for the memory needed to program more general operators. It cites leading-order work on unitaries and measurements and expects free entropy to appear more generally in the order-one term.

This is not a proved universal formula for arbitrary operators or channels. A proposed extension must specify the operator family, encoding model, error criterion, resolution and normalization. The mere existence of a mathematical free entropy does not determine that operational task. Standard microstate free entropy requires a tracial setting; type-III or other non-tracial extensions need separate treatment.

### Several Operators and Free Mutual Information

The Letter expects multivariate free entropy to describe joint programming with the operators' relations known. It also asks about operational meanings of free mutual information. Subadditivity and free-independence identities motivate these questions; they do not themselves prove coding theorems.

### Unknown Spectrum

The Letter quotes the established leading universal memory cost

$$|M_n|=\frac{d^2-1}{2}\log_2n+o(\log n),$$

expects a dimension-dependent order-one term, and leaves a Bayesian free-entropy interpretation of the whole family unspecified. The [[Article]] separately discusses the additional unknown-spectrum cost in `app:unknown_spectrum`. Neither extension is a premise or conclusion of the fixed-spectrum Lean endpoint.

## A Bridge That Is No Longer Merely Open

The current Letter's `rem:bridge` and `eq:bridge` give a **conditional double-scaling derivation** of Voiculescu's entropy. For quantile matrices $X_d$ with nonzero minimum gaps $g_d$ and convergent discrete logarithmic energies, assume

$$\varepsilon_d\to0,\qquad \varepsilon_d=o(g_d),\qquad \log_2\varepsilon_d^{-1}=o(d).$$

Then the manuscript obtains

$$
\chi(x)=\lim_{d\to\infty}\left[
\frac{\chi_{\mathrm{phy}}(X_d;\varepsilon_d)}{d^2}
-\log_2\varepsilon_d^{-1}-\frac12\log_2d\right]
+\frac12\log_2e+\frac12\log_2(2\pi).
$$

This establishes the stated bridge under its regularity and scaling assumptions. It should not remain listed as an entirely unexplored connection, or be read as a theorem for every sequence of finite matrices.

## Historical Notes and Formalization Scope

The older Notes discuss visible-state programming, unitary programming, spectral measurements, expectation-value programming, and possible character-formula corrections. Those document-specific discussions are background, not additional theorems of the current Letter. Their old proof/open-status claims are not certified by this wiki refresh.

The Lean endpoints prove Article Theorems 1 and 2 for actual states and channels. They do not formalize the physical free-entropy volume, the double-scaling bridge, or the broader programming conjectures. See [[formalization|Formalization scope]] and [[proof-structure|Current proof structure]].

## Related

- [[Letter|Current Letter]]
- [[definitions/physical-free-entropy-def|Physical Free Entropy]]
- [[definitions/free-entropy-voiculescu|Voiculescu's Free Entropy]]
- [[concepts/quantum-minimum-description-length|Quantum Minimum Description Length]]
- [[open-questions/degenerate-spectrum|Repeated Positive Eigenvalues]]
