# Positive-Order and Retained-Branch Bounds

**Labels:** `eq:forward_monotonicity`, `eq:branch_trace_comparison`, `eq:positive_deficit_trace` in the current [[Article]].
**Source:** [retaining the highest-weight branch](https://github.com/JWang226/QMDL/blob/main/article.tex#L1364), [positive remainder bound](https://github.com/JWang226/QMDL/blob/main/article.tex#L1686).
**Lean theorem:** [FreeEntropy.TraceDistance.retained_branch_error_bound](https://github.com/JWang226/QMDL/blob/main/lean/FreeEntropy/TraceDistance.lean#L172).

## Statement

Let $A$ be a retained, possibly subnormalized Kraus branch of a state output $\sigma$, so $0\le A\le\sigma$ and $\operatorname{Tr}\sigma=1$. Let $B$ be the target state. The omitted branches are positive and have trace $1-\operatorname{Tr}A$, giving

$$
\frac12\|\sigma-B\|_1
\le\frac12\|A-B\|_1+\frac{1-\operatorname{Tr}A}{2}.
$$

If a positive remainder $R$ satisfies $A\ge B-R$, then

$$
\frac{\|A-B\|_1+1-\operatorname{Tr}A}{2}
=\operatorname{Tr}(B-A)_+
\le\operatorname{Tr}R.
$$

Thus one operator inequality bounds both the retained-branch error and the missing probability mass. For normalized $A$, it directly bounds the ordinary trace distance.

## Intuition

Dropping Kraus branches leaves less positive operator mass than the full output. A fidelity lower bound can exploit this order, but the current proof goes further: it explicitly budgets the missing mass and obtains the needed trace-distance bound without a square-root conversion.

## Proof Sketch

The first inequality is the triangle inequality, using $\|\sigma-A\|_1=\operatorname{Tr}(\sigma-A)$. For the second, use the positive part of $B-A$:

$$
\operatorname{Tr}(B-A)_+
=\max_{0\le L\le I}\operatorname{Tr}[L(B-A)]
\le\max_{0\le L\le I}\operatorname{Tr}(LR)
\le\operatorname{Tr}R.
$$

In the forward cloning proof, the auxiliary identity dominates its highest-weight projector. Therefore the embedded output dominates the retained highest-weight branch. The blockwise Casimir estimates and coefficient comparisons construct $R$; its trace is controlled by dimension loss and mean depth.

## Lean Map

- [FreeEntropy.TraceDistance.positive_remainder_bound](https://github.com/JWang226/QMDL/blob/main/lean/FreeEntropy/TraceDistance.lean#L160): the general trace-norm inequality from positive order.
- [FreeEntropy.TraceDistance.retained_branch_error_bound](https://github.com/JWang226/QMDL/blob/main/lean/FreeEntropy/TraceDistance.lean#L172): normalized target plus the missing-trace term.
- [FreeEntropy.TraceDistance.traceDistance_le_remainder](https://github.com/JWang226/QMDL/blob/main/lean/FreeEntropy/TraceDistance.lean#L182): equal-trace specialization.
- [FreeEntropy.CloningMatrices.traceDistance_le_block_loss](https://github.com/JWang226/QMDL/blob/main/lean/FreeEntropy/CloningMatrices.lean#L56): sums an explicit positive remainder over weight blocks.
- [FreeEntropy.CloningMatrices.forward_traceDistance_le](https://github.com/JWang226/QMDL/blob/main/lean/FreeEntropy/CloningMatrices.lean#L97): allows the retained source coefficients to dominate the target coefficients.

These are reusable intermediate statements with explicit operator premises. The final canonical channel construction proves those premises.

## Relation to the Older Fidelity Lemma

Earlier wiki versions called this “Monotonicity (Lemma 5)” and stated that the root fidelity of a retained Kraus branch is no larger than that of the full output. That is a different useful consequence of positive order, via operator monotonicity of the square root. It describes the older fidelity-based route; the current Article's trace-distance proof uses the displayed remainder inequality. No separate checked proof of that historical fidelity lemma is claimed here.

## Dependencies

- Positive operator order and the trace norm
- Kraus-branch decomposition
- [[results/lemmas/perturbation-lemma|Local projector-deficit bounds]]

## Used By

- [[results/cloning-fidelity|Theorem 2 finite trace-distance estimate]]
