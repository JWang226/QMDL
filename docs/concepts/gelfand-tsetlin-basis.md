# Gelfand-Tsetlin (GT) Basis

**Appears in:** [[Article|current Article]], `lem:kostka` and `lem:shallow_multiplicities`; also [[Notes|the earlier Notes]].

## Intuition

Gelfand-Tsetlin patterns label a distinguished basis, after phase conventions are chosen, for a finite-dimensional irreducible representation of $\mathrm{GL}(d, \mathbb{C})$. It works by restricting the representation down the chain $\mathrm{GL}(d) \supset \mathrm{GL}(d-1) \supset \cdots \supset \mathrm{GL}(1)$. At each step, the irrep breaks into smaller irreps, and the sequence of labels at each level gives a **GT pattern** -- a triangular array of integers that uniquely identifies each basis vector.

## Formal Description

A GT pattern for the irrep $H_\lambda$ (with $\lambda = (\lambda_1, \ldots, \lambda_d)$) is a triangular array:

$$\begin{pmatrix} \lambda_1^{(d)} & & \lambda_2^{(d)} & & \cdots & & \lambda_d^{(d)} \\ & \lambda_1^{(d-1)} & & \lambda_2^{(d-1)} & & \cdots & \lambda_{d-1}^{(d-1)} \\ & & & \ddots & & & \\ & & & & \lambda_1^{(1)} & & \end{pmatrix}$$

where:
- Top row: $\lambda^{(d)} = \lambda$ (the highest weight)
- **Interlacing conditions**: $\lambda_i^{(k)} \geq \lambda_i^{(k-1)} \geq \lambda_{i+1}^{(k)}$ for all valid $i, k$

The **weight** of a GT pattern is $w_i = \sum_j \lambda_j^{(i)} - \sum_j \lambda_j^{(i-1)}$.

## Concrete Example: $\mathrm{GL}(3)$, Irrep $\lambda = (3, 1, 0)$

Consider the irrep $H_{(3,1,0)}$ of $\mathrm{GL}(3)$. A GT pattern has the form:

$$\begin{pmatrix} 3 & & 1 & & 0 \\ & a & & b & \\ & & c & & \end{pmatrix}$$

with interlacing conditions: $3 \geq a \geq 1$, $1 \geq b \geq 0$, and $a \geq c \geq b$. One specific GT pattern is:

$$\begin{pmatrix} 3 & & 1 & & 0 \\ & 2 & & 1 & \\ & & 1 & & \end{pmatrix}$$

**Reading off the weight:** The weight $w = (w_1, w_2, w_3)$ is computed from the row sums:

- Row 3 sum: $3 + 1 + 0 = 4$
- Row 2 sum: $2 + 1 = 3$
- Row 1 sum: $1$

Then $w_3 = 4 - 3 = 1$, $w_2 = 3 - 1 = 2$, $w_1 = 1$. So this basis vector has weight $(1, 2, 1)$.

The total number of valid GT patterns for $H_{(3,1,0)}$ equals $\dim H_{(3,1,0)} = 15$ (by the [[concepts/weyl-dimension-formula|Weyl Dimension Formula]]).

## Role in the Project

GT patterns give combinatorial weight multiplicities and the Article's injection proof of monotonicity. The current highest-weight perturbation argument compares **weight projectors**, not a chosen correspondence between individual GT basis vectors.

The Lean development also proves GT counting results, but its actual physical representation chain constructs orthonormal weight bases and establishes highest-weight cyclicity, PBW bounds, and canonical classification. `CanonicalCharacterIdentity` proves the actual canonical Weyl character identity; `CanonicalDimension` identifies its dimension with the GT count and Weyl product. Thus equality of a combinatorial count and a representation dimension is a theorem, not an assumed identification. The pattern injection is `FreeEntropy.GelfandTsetlin.multiplicity_mono` in [GelfandTsetlin.lean](https://github.com/JWang226/Quantum-Minimum-Description-Length/blob/main/lean/FreeEntropy/GelfandTsetlin.lean). The canonical dimension identification is `FreeEntropy.ExteriorRepresentation.canonical_dimension_eq_GT` in [CanonicalDimension.lean](https://github.com/JWang226/Quantum-Minimum-Description-Length/blob/main/lean/FreeEntropy/CanonicalDimension.lean). For the actual cloning channel, [CartanMultiplicity.lean](https://github.com/JWang226/Quantum-Minimum-Description-Length/blob/main/lean/FreeEntropy/CartanMultiplicity.lean) supplies a separate injective highest-weight slice, and PBW plus explicit exterior monomials give shallow equality. The proof does not assume a chosen correspondence between GT basis vectors and that channel. See [[proof-structure|the current proof map]].

## Related

- [[results/lemmas/kostka-monotonicity|Multiplicity Monotonicity]] -- uses GT pattern injection
- [[results/lemmas/perturbation-lemma|Highest-Weight Subspace Perturbation]] -- compares weight projectors
- [[concepts/schur-weyl-duality|Schur-Weyl Duality]] -- the decomposition where these bases live

## External References

- [Gelfand-Tsetlin basis (Wikipedia)](https://en.wikipedia.org/wiki/Gelfand%E2%80%93Tsetlin_basis)
- I. M. Gelfand and M. L. Tsetlin, "Finite-dimensional representations of the group of unimodular matrices," *Doklady Akad. Nauk SSSR* 71, 825--828 (1950)
- A. I. Molev, *Yangians and Classical Lie Algebras*, AMS Mathematical Surveys and Monographs (2007)
