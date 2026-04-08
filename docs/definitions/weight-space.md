# Weight and Weight Space

**Source:** Article Sec. 6.1; Notes Sec. 4.1

## Statement

A **weight** of a $\mathrm{GL}(d)$ representation is a vector $w = (w_1, \ldots, w_d) \in \mathbb{Z}^d$ such that the maximal torus $T = \{(t_1, \ldots, t_d)\} \subset \mathrm{GL}(d)$ acts on some nonzero vector $v$ by:

$$\pi(t_1, \ldots, t_d) \cdot v = t_1^{w_1} \cdots t_d^{w_d} \cdot v$$

The **weight space** $(H_\lambda)_w$ is the subspace of all such vectors with weight $w$. Its dimension is the [[definitions/kostka-number|Kostka Number]] $K_{\lambda, w}$.

## Weight Offset Convention

In the papers, weights are often parameterized as $w = \lambda - \delta$ where $\delta \in Q_+$ (the positive root lattice) is the **weight offset** from the highest weight $\lambda$. Then $\delta = \sum_\alpha n_\alpha \alpha$ where $\alpha$ ranges over simple roots $\alpha_i = e_i - e_{i+1}$, and $|\delta| = \sum_\alpha n_\alpha$.

## Qubit Example ($d = 2$)

For $d = 2$, the irrep $H_\lambda$ with $\lambda = (\lambda_1, \lambda_2)$ has weights:

$$w_k = (\lambda_1 - k,\, \lambda_2 + k), \quad k = 0, 1, \ldots, \lambda_1 - \lambda_2$$

Each weight space is **1-dimensional**: $K_{\lambda, w_k} = 1$ for all $k$. So $H_\lambda$ decomposes as:

$$H_\lambda = \bigoplus_{k=0}^{\lambda_1 - \lambda_2} (H_\lambda)_{w_k}$$

with $\dim H_\lambda = \lambda_1 - \lambda_2 + 1$. This is just the familiar spin-$J$ representation (with $J = (\lambda_1 - \lambda_2)/2$), where $w_k$ corresponds to the $m = J - k$ eigenvalue of $J_z$.

The maximal torus acts as $\mathrm{diag}(t_1, t_2) \cdot v_k = t_1^{\lambda_1 - k} t_2^{\lambda_2 + k} v_k$.

## Qutrit Example ($d = 3$)

For $d = 3$, the weights of $H_\lambda$ with $\lambda = (\lambda_1, \lambda_2, \lambda_3)$ are vectors $w = (w_1, w_2, w_3) \in \mathbb{Z}^3$ with $w_1 + w_2 + w_3 = \lambda_1 + \lambda_2 + \lambda_3$. These are parameterized as $w = \lambda - \delta$ where $\delta = c_1 \alpha_1 + c_2 \alpha_2 = (c_1, -c_1 + c_2, -c_2)$ with $c_1, c_2 \geq 0$.

For the fundamental representation $\lambda = (1, 0, 0)$: the weights are $(1,0,0)$, $(0,1,0)$, $(0,0,1)$, each 1-dimensional. $\dim H_{(1,0,0)} = 3$.

For the adjoint representation $\lambda = (2, 1, 0)$: the weights include $(2,1,0)$ (highest, dim 1), $(2,0,1)$, $(1,2,0)$, $(1,1,1)$ (dim 2), $(0,2,1)$, $(1,0,2)$, $(0,1,2)$ (lowest, dim 1). The weight $(1,1,1)$ has multiplicity $K_{(2,1,0),(1,1,1)} = 2$, illustrating that weight spaces can be multi-dimensional for $d \geq 3$.

## Role in the Project

The [[results/cloning-fidelity|Cloning Fidelity (Theorem 1)]] proof decomposes the fidelity weight-by-weight. For each weight offset $\delta$:
- The "quantum" contribution depends on the angle between weight spaces of $H_\mu$ and $H_\nu$ -- specifically, the overlap between the weight-$(\mu-\delta)$ subspace of $H_\mu$ (embedded via the isometry $V$ into $H_\mu \otimes H_\omega$) and the weight-$(\nu-\delta)$ subspace of $H_\nu$.
- The "classical" contribution depends on the probability $p_\mu(\delta) = x^{\mu-\delta}/s_\mu(x)$ and the corresponding $p_\nu(\delta)$.

For qubits ($d = 2$), all weight spaces are 1-dimensional, so the quantum contribution is trivial (perfect alignment). The cloning error is purely classical. For $d \geq 3$, multi-dimensional weight spaces introduce genuine quantum alignment errors, making the analysis substantially harder.

## Used By

- [[concepts/gelfand-tsetlin-basis|Gelfand-Tsetlin Basis]]
- [[definitions/kostka-number|Kostka Number]]
- [[results/cloning-fidelity|Cloning Fidelity (Theorem 1)]]
- [[results/perturbation-lemma|Perturbation Lemma (Lemma 7)]]

## External References

- [Weight (representation theory) (Wikipedia)](https://en.wikipedia.org/wiki/Weight_(representation_theory))
- [Humphreys, *Introduction to Lie Algebras and Representation Theory* (Springer, 1972)](https://doi.org/10.1007/978-1-4612-6398-2)
