# Kostant Partition Function

**Appears in:** Article (Appendix), Notes

## Definition

The **Kostant partition function** $\mathfrak{K}(\delta)$ counts the number of ways to write $\delta \in Q_+$ (the positive root lattice) as a sum of positive roots:

$$\mathfrak{K}(\delta) = \#\{(n_\alpha)_{\alpha \in \Phi^+} : \sum_\alpha n_\alpha \alpha = \delta, n_\alpha \in \mathbb{Z}_{\geq 0}\}$$

## Relation to Kostka Numbers

By Kostant's weight multiplicity formula:

$$K_{\lambda, w} = \sum_{w \in W} (-1)^{l(w)} \mathfrak{K}(w(\lambda + \rho_W) - (w_0 + \rho_W))$$

where $W$ is the Weyl group and $\rho_W$ is the Weyl vector. In particular, $K_{\lambda, \lambda-\delta} \leq \mathfrak{K}(\delta)$ (each Kostka number is bounded by the partition function).

## Example: $A_2$ (i.e., $\mathrm{GL}(3)$)

For $\mathrm{GL}(3)$, the positive roots are $\Phi^+ = \{\alpha_1, \alpha_2, \alpha_1 + \alpha_2\}$, where $\alpha_1 = e_1 - e_2$ and $\alpha_2 = e_2 - e_3$ are the simple roots.

**Compute $\mathfrak{K}(\alpha_1 + \alpha_2)$:** We need the number of ways to write $\delta = \alpha_1 + \alpha_2$ as a non-negative integer combination of positive roots:

$$n_1 \alpha_1 + n_2 \alpha_2 + n_3(\alpha_1 + \alpha_2) = \alpha_1 + \alpha_2$$

This gives $(n_1 + n_3)\alpha_1 + (n_2 + n_3)\alpha_2 = \alpha_1 + \alpha_2$, so $n_1 + n_3 = 1$ and $n_2 + n_3 = 1$. The solutions are:

| $n_1$ | $n_2$ | $n_3$ | Decomposition |
|---|---|---|---|
| 1 | 1 | 0 | $\alpha_1 + \alpha_2$ |
| 0 | 0 | 1 | $(\alpha_1 + \alpha_2)$ |

So $\mathfrak{K}(\alpha_1 + \alpha_2) = 2$. This means the weight space at depth $\alpha_1 + \alpha_2$ below the highest weight in a Verma module has dimension 2.

## Generating Function

The generating function for the Kostant partition function organized by height $t = |\delta|$ is:

$$\sum_{t \geq 0} A_r(t) \, q^t = \prod_{\alpha \in \Phi^+} \frac{1}{1 - q^{|\alpha|}}$$

where $A_r(t) = \sum_{|\delta| = t} \mathfrak{K}(\delta)$. For type $A_{r-1}$, there are exactly $r - h$ positive roots of height $h$, so:

$$\sum_{t \geq 0} A_r(t) \, q^t = \prod_{h=1}^{r-1} \frac{1}{(1-q^h)^{r-h}}$$

This gives the crude bound $A_r(t) \leq C_r (t+1)^{r(r-1)/2 - 1}$, which is the polynomial prefactor controlling the tail mass.

## Role in the Project

The Kostant partition function provides the **upper bound** on weight multiplicities used in the [[results/tail-mass|Tail Mass (Lemma 8)]] proof. Since the irrep $H_\mu$ is a quotient of the Verma module $M(\mu)$, each weight multiplicity satisfies $K_{\mu, \mu - \delta} \leq \mathfrak{K}(\delta)$. The generating function analysis of $\mathfrak{K}(\delta)$ gives the polynomial prefactor $T^\kappa$ (with $\kappa = r(r-1)/2 - 1$) controlling the tail mass bound.

## Related

- [[results/tail-mass|Tail Mass (Lemma 8)]]
- [[definitions/kostka-number|Kostka Number]]
- [[results/kostka-monotonicity|Kostka Number Monotonicity (Lemma 3)]]
