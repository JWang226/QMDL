/-
Copyright (c) 2026 Free Entropy formalization contributors.
See LICENSE and NOTICE in the repository root for license and attribution.
-/

import FreeEntropy.Proofs

/-!
# Theorem 1 with the exact spectrum and padded target

The conclusions below have the manuscript's precise `L_{d,r}` and its precise
padded rows. They remain conditional on quantum inputs: existence of the
code, identification of a Weyl product as a representation dimension, and
the finite trace-distance and memory estimates. These are not assumptions
about the asymptotic conclusion itself.
-/

noncomputable section
open Filter
open scoped Topology BigOperators
namespace FreeEntropy

/-- A fixed, normalized spectrum of the kind assumed by both theorems.
Indices `0,...,r-1` carry the positive eigenvalues. -/
structure FixedSpectrum (d r : ℕ) where
  rank_pos : 0 < r
  rank_le : r ≤ d
  eigenvalue : ℕ → ℝ
  positive : ∀ i, i < r → 0 < eigenvalue i
  decreasing : ∀ i j, i < j → j < r → eigenvalue j < eigenvalue i
  zero_padded : ∀ i, r ≤ i → i < d → eigenvalue i = 0
  normalized : ∑ i ∈ Finset.range r, eigenvalue i = 1

namespace FixedSpectrum

theorem active_gap {d r : ℕ} (s : FixedSpectrum d r) :
    ∀ i j, i < r → i < j → j < d → s.eigenvalue j < s.eigenvalue i := by
  intro i j hi hij hj
  by_cases hjr : j < r
  · exact s.decreasing i j hij hjr
  · rw [s.zero_padded j (Nat.le_of_not_gt hjr) hj]
    exact s.positive i hi

/-- The target in equation `target_rep`, translated from one-based indexing. -/
def targetRow {d r : ℕ} (s : FixedSpectrum d r) (n i : ℕ) : ℝ :=
  if i < r then (paddedRow n (s.eigenvalue i) (typicalWidth n) (r - i : ℕ) : ℝ) else 0

theorem targetRow_normalized_tendsto {d r : ℕ} (s : FixedSpectrum d r)
    (i : ℕ) (hi : i < d) :
    Tendsto (fun n => s.targetRow n i / (n : ℝ)) atTop (𝓝 (s.eigenvalue i)) := by
  by_cases hir : i < r
  · simpa only [targetRow, hir, ↓reduceIte] using
      paddedRow_normalized_tendsto (s.eigenvalue i) (r - i : ℕ) typicalWidth_div_tendsto_zero
  · simp only [targetRow, hir, ↓reduceIte, zero_div,
      s.zero_padded i (Nat.le_of_not_gt hir) hi]
    exact tendsto_const_nhds

end FixedSpectrum

/-- Theorem 1's exact achievable expansion and error rate, conditional on
the existence and finite estimates of the prescribed quantum protocol.
The normalized-row limit and all factorial/eigenvalue terms are proved. -/
theorem theorem1_achievability_of_quantum_estimates
    {d r : ℕ} (s : FixedSpectrum d r) (memory : ℕ → ℕ) (δ : ℕ → ℝ) (C : ℝ)
    (hdim : ∀ᶠ n in atTop,
      (memory n : ℝ) = Weyl.activeProduct d r (s.targetRow n))
    (hδ0 : ∀ᶠ n in atTop, 0 ≤ δ n)
    (herror : ∀ᶠ n in atTop, δ n ≤ 2 * (C * Weyl.errorScale n) +
      2 * Concentration.tailBound (r * (r + 1) / 2) n) :
    Tendsto (fun n => Real.logb 2 (memory n) - Weyl.qmdl d r s.eigenvalue n) atTop (𝓝 0) ∧
      Asymptotics.IsBigO atTop δ Weyl.errorScale ∧ Tendsto δ atTop (𝓝 0) := by
  have h := theorem1_achievability_of_estimates d r s.targetRow s.eigenvalue
    memory δ C (r * (r + 1) / 2) s.active_gap s.targetRow_normalized_tendsto hdim hδ0 herror
  simpa only [Weyl.rootLeading_eq_qmdl d r s.rank_le s.eigenvalue _
    s.active_gap s.zero_padded] using h

/-- Theorem 1's exact liminf converse, conditional on transferring a quantum
code to the padded representation and applying its orbit memory bound. -/
theorem theorem1_converse_of_quantum_estimates
    {d r : ℕ} (s : FixedSpectrum d r) (memory target : ℕ → ℕ)
    (δ e : ℕ → ℝ) (γ : ℝ)
    (hdim : ∀ᶠ n in atTop,
      (target n : ℝ) = Weyl.activeProduct d r (s.targetRow n))
    (htarget : ∀ n, 0 < target n) (hγ : 0 < γ)
    (hδ : Tendsto δ atTop (𝓝 0)) (he : Asymptotics.IsBigO atTop e Weyl.errorScale)
    (hbound : ∀ᶠ n in atTop,
      (target n : ℝ) * (1 - (δ n + e n) / γ) ≤ memory n) :
    (0 : EReal) ≤ liminf
      (fun n => ((Real.logb 2 (memory n) - Weyl.qmdl d r s.eigenvalue n : ℝ) : EReal)) atTop := by
  have h := theorem1_converse_of_estimates d r s.targetRow s.eigenvalue
    memory target δ e γ s.active_gap s.targetRow_normalized_tendsto
    hdim htarget hγ hδ he hbound
  simpa only [Weyl.rootLeading_eq_qmdl d r s.rank_le s.eigenvalue _
    s.active_gap s.zero_padded] using h

end FreeEntropy
