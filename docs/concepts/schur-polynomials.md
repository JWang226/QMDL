# Schur Polynomials

**Appears in:** [[Article|current Article]], sector probabilities `eq:qlambda_def`, weight decomposition `sec:prelim`, and eigenvalue ratio `lem:ratio`; also [[Notes|the earlier Notes]].

## Intuition

For a partition $\lambda$, the Schur polynomial $s_\lambda(x_1,\ldots,x_d)$ is the character of the polynomial irreducible representation. It gives the trace used to normalize its representation state. In a tensor-power source, the probability of an entire Schur–Weyl sector also includes the number of copies of that representation.

For $\rho^{\otimes n}$ and $\lambda\vdash n$, if $f^\lambda$ is the dimension of the symmetric-group multiplicity register, then

$$q_\lambda=f^\lambda s_\lambda(x),\qquad
\rho_\lambda=\frac{\pi_\lambda(\rho)}{s_\lambda(x)}.$$

Thus $s_\lambda(x)$ alone is not generally the sector probability. For a rank-$r$ source, the normalized state here is used for partitions with at most $r$ rows, where the denominator is positive.

## Definition and character formulas

The weight expansion defines a polynomial on all $x$:

$$s_\lambda(x)=\sum_w K_{\lambda,w}x^w
=\operatorname{Tr}\pi_\lambda(\operatorname{diag}x).$$

For pairwise distinct coordinates it also has the alternant expression

$$s_\lambda(x)=
\frac{\det[x_j^{\lambda_i+d-i}]_{i,j=1}^d}
{\det[x_j^{d-i}]_{i,j=1}^d}
=\frac{\det[x_j^{\lambda_i+d-i}]}{\prod_{i<j}(x_i-x_j)}.$$

When coordinates coincide, including repeated zeros in a rank-deficient spectrum, the quotient is interpreted by its polynomial extension. The determinant numerator identity remains a polynomial identity; substituting directly into a zero denominator is not the definition.

## Role in the current proof

The coefficients $K_{\lambda,w}$ are weight multiplicities. Writing $w=\lambda-\delta$, the eigenvalue on that weight space is $p_\lambda(\delta)=x^{\lambda-\delta}/s_\lambda(x)$, and its total probability is $K_{\lambda,w}p_\lambda(\delta)$.

For dominant $\omega=\nu-\mu$, the ratio

$$Z(x)=\frac{x^\omega s_\mu(x)}{s_\nu(x)}$$

compares those individual eigenvalues at the same offset. The current [[results/lemmas/probability-ratio|eigenvalue-ratio lemma]] bounds $1-Z$ using multiplicity monotonicity, shallow equality and uniform mean depth. It does not require the older exponential determinant-dominance argument.

The character formula also yields the exact representation dimension, $s_\lambda(1,\ldots,1)=d_\lambda$, and its [[results/lemmas/weyl-dimension-asymptotic|Weyl asymptotic]]. For physical sector concentration, the proof combines bounds on the normalized representation block with actual copy counts; the multiplicity factor is included before estimating the total atypical mass.

## Lean route

`FreeEntropy.ExteriorRepresentation.canonicalCharacter_identity_all` in [CanonicalCharacterIdentity.lean](https://github.com/JWang226/QMDL/blob/main/lean/FreeEntropy/CanonicalCharacterIdentity.lean) proves the polynomial numerator identity for the constructed canonical representation. [WeylDimensionExtraction.lean](https://github.com/JWang226/QMDL/blob/main/lean/FreeEntropy/WeylDimensionExtraction.lean) and [CanonicalDimension.lean](https://github.com/JWang226/QMDL/blob/main/lean/FreeEntropy/CanonicalDimension.lean) extract its actual dimension.

`FreeEntropy.SchurWeyl.canonicalMonomialState_eq_relativeState` in [CanonicalMonomialState.lean](https://github.com/JWang226/QMDL/blob/main/lean/FreeEntropy/CanonicalMonomialState.lean) connects normalized monomials with the weight-coordinate state used in cloning. These are proved connections to concrete representations, not assumed Schur-character inputs to the final endpoint.

## Related

- [[concepts/schur-weyl-duality|Schur–Weyl sectors and their multiplicities]]
- [[results/lemmas/kostka-monotonicity|Weight multiplicity monotonicity]]
- [[results/lemmas/probability-ratio|Eigenvalue ratio]]
- [[results/lemmas/sanov-theorem|Physical sector concentration]]
- [[proof-structure|Current proof map]]

## External references

- I. G. Macdonald, *Symmetric Functions and Hall Polynomials*, second edition, Oxford University Press (1995).
- R. P. Stanley, *Enumerative Combinatorics, Volume 2*, Cambridge University Press (1999).
- W. Fulton, *Young Tableaux*, Cambridge University Press (1997).
