# Free Probability Theory

**Appears in:** [[Letter]] (Introduction and Discussion); historical [[Notes]].

## Free Independence

Free probability studies noncommuting random variables in a tracial probability space. Unital subalgebras $(\mathcal A_i)$ are freely independent when

$$\tau(a_1\cdots a_k)=0$$

whenever $\tau(a_j)=0$, $a_j\in\mathcal A_{i_j}$, and successive indices differ: $i_j\ne i_{j+1}$. This condition determines mixed moments from the separate distributions.

Tensor independence instead combines commuting subsystem algebras with a product state. The two independence notions have different moment rules. Freeness should not be identified with ordinary statistical independence, nor with independence between a matrix's eigenvalue list and its eigenbasis.

## Entropy and Microstates

Voiculescu's [[concepts/free-entropy|free entropy]] counts matrix microstates that approximately reproduce a tracial noncommutative distribution. In the current Letter's single-variable definition (`eq:free_ent`), the microstates are bounded self-adjoint matrices, constrained in every moment up to a cutoff. Lebesgue volume, normalized by matrix size, replaces the number of typical strings in Shannon's formula.

The definition depends on a trace. It therefore does not directly apply to a type III algebra without a separate non-tracial extension. Moment constraints also make sense for several noncommuting variables, even though those variables have no joint spectral distribution.

For freely independent families, free entropy is additive, paralleling entropy additivity for tensor products. The Letter discusses this as a possible guide to more general programming tasks, not as an assumption in its finite-state compression theorem.

## Random Matrices and Dynamics

Suitable independent random-matrix ensembles become asymptotically free in the large-matrix limit. Independence alone is not a sufficient statement for arbitrary matrix ensembles. Likewise, observables at different times can become asymptotically free in suitable large-system chaotic limits; time separation by itself does not imply freeness.

For a single Hermitian matrix, changing to eigenvalue–eigenvector coordinates produces a squared [[concepts/vandermonde-determinant|Vandermonde determinant]] and an invariant orbit measure. This change of variables explains the logarithmic energy in the single-variable entropy formula. It does not require a claim that eigenvalues and eigenvectors are freely independent.

## Role in the Project

The Letter defines a finite-dimensional [[concepts/physical-free-entropy|physical free entropy]] by a Hilbert–Schmidt tube-volume ratio. For known spectra with distinct positive eigenvalues, it relates this quantity at resolution $n^{-1}$ to optimal [[concepts/quantum-minimum-description-length|QMDL]], with an explicit additive constant.

The Article and Lean formalization prove the compression theorem used in this comparison. The geometric volume relation and the conditional large-dimension bridge to Voiculescu's entropy are additional Letter arguments. Multivariate programming, free mutual information, and the broader operational meaning of freeness remain discussion or conjectural directions; see [[proof-structure]] and [[open-questions/free-entropy-conjecture]].

## Related

- [[concepts/free-entropy|Free Entropy]]
- [[concepts/free-entropy-dimension|Free Entropy Dimension]]
- [[concepts/semicircular-element|Semicircular Element and Free Independence]]

## References

- `voiculescu1994analogues`: Voiculescu's microstate free entropy and additivity results.
- `voiculescu2002free`: Voiculescu, "Free entropy" (survey, 2002).
- `hiai2000semicircle`: Hiai and Petz, *The Semicircle Law, Free Random Variables and Entropy*.
- `vardhan2025`: The dynamics and free-mutual-information work cited in the Letter.
