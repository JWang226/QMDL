# Kirillov–Kostant–Souriau (KKS) Geometry

**Appears in:** [[Letter]] (discussion following `eq:result_const` and `eq:weyl_geometry`); historical [[Notes]].

## Symplectic Structure

A coadjoint orbit carries the Kirillov–Kostant–Souriau symplectic form. For $U(d)$, a fixed-spectrum orbit of Hermitian matrices is such an orbit. Integral dominant weights label the representations that enter geometric quantization; an arbitrary real spectrum does not itself label a finite-dimensional representation.

The current Letter uses this geometry to explain the different eigenvalue-gap factors in an orbit's Hilbert–Schmidt volume and in the dimension of the representation retained by the compression code.

## Two Volume Forms

For a full-rank state with distinct eigenvalues $p_1>\cdots>p_d$, write $\Delta(p)=\prod_{i<j}(p_i-p_j)$. A tangent vector has the form $[K,\rho]$, where $K$ is anti-Hermitian, and

$$[K,\rho]_{ij}=(p_j-p_i)K_{ij}.$$

The complex coordinate $K_{ij}$ has two real directions. Hilbert–Schmidt volume weights both by the gap, giving a factor $\Delta(p)^2$. The KKS form pairs these two directions and contributes one gap per pair to symplectic volume, giving a factor $\Delta(p)$.

This compares the dependence on spectral gaps. It does not assert that symplectic volume is literally the square root of Riemannian volume with no normalization constants, or that Hilbert-space dimension is half of the real orbit dimension.

## The Representation Dimension

For the integer target partitions used by the code, $\Lambda/n\to p$. Weyl's dimension formula gives the actual asymptotic statement

$$\dim H_\Lambda=[1+o(1)]\,
\frac{n^{d(d-1)/2}\Delta(p)}{\prod_{k=1}^{d-1}k!}.$$

Taking its logarithm gives the Article's optimal memory cost. The Letter compares that result with its tube-volume expansion and obtains, for an attaining code sequence,

$$|M_n|=\frac12\chi_{\mathrm{phy}}(\rho;n^{-1})+C_{d,d}+o(1),$$

where $|M_n|=\log_2\dim M_n$ and

$$C_{d,d}=-\frac12\sum_{k=1}^{d-1}\log k!
-\frac12\log\frac{\Gamma(d^2/2+1)}{\Gamma(d/2+1)}
-\frac{d(d-1)}4\log2.$$

This is the source's `eq:result` and `eq:result_const`. The resolution $n^{-1}$ in the volume comparison is distinct from the angular distinguishability scale $n^{-1/2}$. For rank-deficient states with distinct positive eigenvalues, see the explicit $C_{d,r}$ in [[concepts/quantum-minimum-description-length]].

## Scope

The Lean proof establishes the representation dimensions and the optimal compression cost by algebraic and analytic arguments. It does not formalize KKS geometry or the Letter's tube-volume calculation. The Letter also conjectures programming extensions beyond states; it does not prove them from this geometric interpretation. See [[proof-structure]] and [[open-questions/free-entropy-conjecture]].

## Related

- [[concepts/physical-free-entropy|Physical Free Entropy]]
- [[concepts/flag-manifold|Flag Manifold]]
- [[concepts/weyl-dimension-formula|Weyl Dimension Formula]]
- [[concepts/vandermonde-determinant|Vandermonde Determinant]]

## Reference

- `kirillov2004orbit`: A. A. Kirillov, *Lectures on the Orbit Method*, AMS (2004).
