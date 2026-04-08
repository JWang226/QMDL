# Flag Manifold

**Appears in:** [[Letter]], [[Article]]

## Definition

The **(partial) flag manifold** associated to a partition of $d$ into blocks of sizes $g_1, \ldots, g_m$ is the coset space:

$$\mathrm{Fl}(g_1, \ldots, g_m) = U(d) / (U(g_1) \times U(g_2) \times \cdots \times U(g_m))$$

Its real dimension is $d^2 - \sum_a g_a^2$.

## Intuition

The flag manifold parameterizes all possible **eigenbases** of a Hermitian operator with a given degeneracy structure. If $\rho$ has eigenvalues with multiplicities $g_1, g_2, \ldots, g_m$, then the set of all density matrices with the same spectrum as $\rho$ is exactly the flag manifold $U(d)/(U(g_1) \times \cdots \times U(g_m))$. The stabilizer $U(g_1) \times \cdots \times U(g_m)$ consists of unitaries that rotate within each eigenspace (which doesn't change the operator).

## Dimensional Counting

Start with $U(d)$, which has real dimension $d^2$. Each block $U(g_a)$ in the stabilizer has real dimension $g_a^2$. The stabilizer $U(g_1) \times \cdots \times U(g_m)$ has total dimension $\sum_a g_a^2$. By the theory of coset spaces:

$$\dim_{\mathbb{R}} \mathrm{Fl}(g_1, \ldots, g_m) = d^2 - \sum_a g_a^2$$

Each $U(g_a)$ factor "removes" $g_a^2$ real parameters -- the $g_a^2$ degrees of freedom corresponding to rotations within the $a$-th eigenspace that leave $\rho$ invariant.

## Special Cases

- **Full flag manifold** ($g_i = 1$ for all $i$, i.e., non-degenerate spectrum): $U(d)/U(1)^d$, dimension $d^2 - d = d(d-1)$. The stabilizer consists of $d$ independent phase rotations.

- **Grassmannian** ($m = 2$, $g_1 = k$, $g_2 = d-k$): $U(d)/(U(k) \times U(d-k))$, dimension $2k(d-k)$. This is the space of $k$-dimensional subspaces of $\mathbb{C}^d$.

- **Rank-$r$ non-degenerate state** ($g_1 = \cdots = g_r = 1$, $g_{r+1} = d-r$): dimension $d^2 - r - (d-r)^2 = r(2d - r - 1)$. This is the most common case in the QMDL problem.

## Worked Example: $d = 3$, Rank-2 Non-Degenerate State

Consider a qutrit state $\rho$ with spectrum $p_1 > p_2 > 0 = p_3$ (rank 2, non-degenerate positive eigenvalues). The degeneracy structure is $g_1 = 1, g_2 = 1, g_3 = 1$ -- wait, the zero eigenvalue has multiplicity $d - r = 1$ as well. So the partition is $(1, 1, 1)$, giving the full flag manifold? No: the correct grouping is that the two nonzero eigenvalues are distinct (each with $g = 1$) and the zero eigenvalue has $g_0 = d - r = 1$. The stabilizer is $U(1) \times U(1) \times U(1) = U(1)^3$.

$$\dim_{\mathbb{R}} = d^2 - \sum g_a^2 = 9 - 3 = 6$$

Alternatively, using the rank-$r$ formula: $r(2d - r - 1) = 2(2 \cdot 3 - 2 - 1) = 2 \cdot 3 = 6$.

The QMDL leading term is $\frac{1}{2} \times 6 \times \log n = 3 \log n$ qubits. This matches: the eigenbasis of a rank-2 qutrit lives on a 6-real-dimensional manifold, and geometric quantization halves the dimension.

Now consider a full-rank qutrit $\rho$ with $p_1 > p_2 > p_3 > 0$. The stabilizer is $U(1)^3$, dimension $= 9 - 3 = 6$, and QMDL $= 3\log n$. This is the same because both cases have the same degeneracy structure (all eigenvalues distinct).

For a qutrit projector $\rho = \frac{1}{2}(|0\rangle\langle 0| + |1\rangle\langle 1|)$, the spectrum is $(1/2, 1/2, 0)$ with degeneracies $g_1 = 2, g_2 = 1$. The stabilizer is $U(2) \times U(1)$, dimension $= 9 - 4 - 1 = 4$. QMDL $= 2\log n$, reflecting the smaller orbit (the Grassmannian $\mathrm{Gr}(2,3)$).

## Connection to the KKS Theorem

The flag manifold is a **coadjoint orbit** of $U(d)$. The [[concepts/kks-theorem|KKS Theorem]] (Kirillov-Kostant-Souriau) equips it with a natural symplectic structure, and geometric quantization of this symplectic manifold produces the irrep $H_\lambda$. The key consequence is:

$$\dim H_\lambda \sim \mathrm{Vol}(\mathcal{O}_\lambda)^{1/2}$$

in appropriate units. More precisely, the symplectic volume of the coadjoint orbit is controlled by the Vandermonde determinant $\prod_{i<j}(x_i - x_j)^2$, and taking the square root yields the Weyl dimension. This is why there is a **factor of 1/2** between the real dimension of the flag manifold and the leading $\log n$ coefficient:

$$\log|M_n| = \frac{1}{2} \dim_{\mathbb{R}} \mathrm{Fl} \times \log n + O(1)$$

## Connection to Free Entropy Dimension

The real dimension of the flag manifold relates directly to the [[concepts/free-entropy-dimension|Free Entropy Dimension]]:

$$\dim_{\mathbb{R}} \mathrm{Fl}(g_1, \ldots, g_m) = d^2 - \sum_a g_a^2 = d^2 \cdot \delta(\rho)$$

where $\delta(\rho) = 1 - \sum_a g_a^2/d^2$ is the free entropy dimension from Voiculescu's theory. This provides the bridge between the operator-algebraic notion (free entropy dimension) and the geometric notion (flag manifold dimension).

## Related

- [[concepts/free-entropy-dimension|Free Entropy Dimension]] -- $\delta(\rho) = \dim \mathrm{Fl} / d^2$
- [[concepts/kks-theorem|KKS Theorem]] -- geometric quantization of flag manifolds
- [[concepts/observable-programming|Observable Programming]] -- programming rate governed by flag manifold dimension
- [[concepts/quantum-minimum-description-length|Quantum Minimum Description Length]] -- compression rate governed by $\frac{1}{2}\dim \mathrm{Fl} \cdot \log n$
- [[concepts/weyl-dimension-formula|Weyl Dimension Formula]] -- the leading $\log n$ coefficient is $\frac{1}{2}\dim \mathrm{Fl}$

## External References

- [Flag manifold (Wikipedia)](https://en.wikipedia.org/wiki/Flag_manifold)
- [Generalized flag variety (Wikipedia)](https://en.wikipedia.org/wiki/Generalized_flag_variety)
- [W. Fulton and J. Harris, *Representation Theory: A First Course*, Graduate Texts in Mathematics, Springer (1991)](https://doi.org/10.1007/978-1-4612-0979-9)
- [Grassmannian (Wikipedia)](https://en.wikipedia.org/wiki/Grassmannian)
