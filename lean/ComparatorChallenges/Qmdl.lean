/-
Copyright (c) 2026 Free Entropy formalization contributors.
See LICENSE and NOTICE in the repository root for license and attribution.
-/

import Mathlib

/-! Independent expected definition in a separate compilation unit, preserving
Lean’s generated closed-proof names for strict upstream Comparator matching. -/
noncomputable section
open scoped BigOperators
namespace FreeEntropy.Weyl
noncomputable def qmdl (d r : ℕ) (x : ℕ → ℝ) (n : ℕ) : ℝ :=
  (r : ℝ) * (2 * (d : ℝ) - (r : ℝ) - 1) / 2 * Real.logb 2 n +
    (∑ i ∈ Finset.range r, ∑ j ∈ Finset.Ico (i + 1) r,
      Real.logb 2 (x i - x j)) +
    ((d - r : ℕ) : ℝ) * (∑ i ∈ Finset.range r, Real.logb 2 (x i)) -
    ∑ k ∈ Finset.Ico (d - r) d, Real.logb 2 (k.factorial : ℝ)
end FreeEntropy.Weyl
