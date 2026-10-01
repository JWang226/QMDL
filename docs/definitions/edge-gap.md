# Edge Gap

**Source:** [[Article]], `thm:main`, `lem:shallow_multiplicities`; [[Notes]] uses an earlier full-row convention.

## Statement

Two related gaps occur in the current Article. For a partition $\mu$ with at most $r$ nonzero rows in ambient dimension $d\ge2$, the gap in Theorem 2 is

$$b_\mu=\min_{1\le i\le\min(r,d-1)}(\mu_i-\mu_{i+1}).$$

When $r<d$, this includes the boundary $\mu_r-\mu_{r+1}=\mu_r$, but excludes pairs of empty rows. When $r=d$, it includes all adjacent pairs.

For the shallow-multiplicity argument, $r\ge2$ and

$$g_\mu=\min_{1\le i<r}(\mu_i-\mu_{i+1}).$$

Thus $b_\mu\le g_\mu$. For $r=1$, no internal supported gap is needed: only the zero supported root offset occurs. Theorem 2 uses $b_\mu=\mu_1$ when $d\ge2$; $d=1$ is handled separately.

## Intuition

For a typical partition near $nx$, every relevant gap is linear in $n$ because the positive eigenvalues are strictly decreasing and the last positive eigenvalue is positive. Repeated **zero** eigenvalues do not invalidate this argument. Taking the minimum over all $d-1$ pairs would incorrectly give zero for many rank-deficient sources.

## Role in the Proof

The shallow-multiplicity lemma gives $m_\mu(\delta)=\mathsf P_r(\delta)$ when the supported root depth satisfies $|\delta|\le g_\mu$. Together with the localized Casimir gap, this controls the trace lost from the retained cloning branch. The finite error is bounded by $C_{d,x}\|\nu-\mu\|_1/(b_\mu+1)$, including $b_\mu=0$; small error requires the numerator to be small relative to the gap.

In Lean, `minimumRowGap` in `CanonicalRowBounds.lean` is the exact natural-number version of $b_\mu$. `TypicalRows` proves the eventual uniform lower bound for actual typical rows; this is not an extra assumption in Theorem 1. See [[proof-structure]].

## Example

For $d=4$, $r=2$, and $\mu=(7,3,0,0)$, $b_\mu=\min(4,3)=3$ and $g_\mu=4$. The unrelated zero-to-zero gap is excluded.

## Used By

- [[definitions/scaling-regime|Scaling Regime]]
- [[results/lemmas/kostka-monotonicity|Multiplicity Monotonicity]]
- [[results/lemmas/perturbation-lemma|Highest-Weight Subspace Perturbation]]
- [[results/cloning-fidelity|Cloning Accuracy (Article Theorem 2)]]
