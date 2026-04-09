# Conjecture: Free Entropy as Universal QMDL

**Source:** Letter, line ~248
**Status:** Conjectured

## Conjecture Statement (from the Letter)

> We conjecture that free entropy describes the quantum minimum description length of **any** operator in quantum mechanics.

More precisely: for any family of operators (density matrices, unitaries, Hermitian operators, or more general objects like CPTP maps) parameterized by continuous parameters, the optimal program size for storing a universal program scales as:

$$\log D = \frac{1}{2}\chi_{\mathrm{phy}}(\text{operator}; \varepsilon) + O(1)$$

where $\chi_{\mathrm{phy}}$ is the physical free entropy of the operator, and the relevant information-theoretic task is **programming**: finding the minimum-size quantum memory needed to store a universal program for any instance drawn from the family.

The word "any" here is significant. Free entropy, unlike von Neumann entropy, is defined not just for density operators but for **any element of a non-commutative algebra** -- unitaries, Hermitian operators, even collections of non-commuting operators. This universality of the mathematical definition is conjectured to match a universality of the operational meaning.

## Evidence

The project establishes this for three classes:
1. **Density matrices** (state compression): fully proved with tight $O(1)$ bounds -- the QMDL is $\frac{1}{2}\chi_{\mathrm{phy}}(\rho; n^{-1/2}) + O(1)$
2. **Unitary operators** (unitary programming): proved at leading order -- $\log D = \frac{f}{2}\log(1/\varepsilon) + O(1)$, where $f$ is the number of free parameters (matching $\frac{1}{2}\chi_{\mathrm{phy}}$ at leading order)
3. **Hermitian operators** (observable programming): proved at leading order for spectral measurements -- $\log D = \frac{d^2 \delta(H)}{2}\log(1/\varepsilon) + O(1)$

In all three cases, the leading-order coefficient is $\frac{1}{2}$ times the [[concepts/free-entropy-dimension|Free Entropy Dimension]], which is the leading coefficient of the physical free entropy.

## What Remains

- **$O(1)$ corrections for unitaries and observables**: The subleading term should be $\frac{1}{2}\chi_{\mathrm{reg}}$, the regularized free entropy. See [[open-questions/programming-extensions|Open: Programming Extensions]].
- **Expectation converse**: The converse for observable expectation programming is open. See [[open-questions/programming-extensions|Open: Programming Extensions]].
- **Extension to quantum channels**: Free entropy can be defined for CPTP maps; the corresponding programming task is channel programming.
- **Infinite-dimensional connection**: Relating $\chi_{\mathrm{phy}}$ (defined for finite $d$) to Voiculescu's free entropy $\chi$ (defined in the von Neumann algebra setting as $d \to \infty$).
- **Multivariate free entropy**: The conjecture extends to *multiple* operators: the multivariate free entropy $\chi(a_1, \ldots, a_k)$ should be the QMDL for jointly programming multiple operators, given knowledge of all their relations. Free entropy is subadditive, with equality for freely independent operators (where knowing one operator does not help describe the other).

## Related

- [[concepts/free-entropy|Free Entropy]]
- [[concepts/quantum-minimum-description-length|Quantum Minimum Description Length]]
- [[open-questions/programming-extensions|Programming Extensions (Notes)]]

## External References

- [Voiculescu, "Free entropy" (survey, 2002)](https://doi.org/10.1112/S0024609301008992)
