/-
Copyright (c) 2026 Free Entropy formalization contributors.
See LICENSE and NOTICE in the repository root for license and attribution.
-/

import FreeEntropy.OccupationForward
import FreeEntropy.OccupationCounting
import FreeEntropy.Cloning

/-! The explicit finite error rate of pure-state occupation cloning. -/

noncomputable section
open scoped BigOperators

namespace FreeEntropy.OccupationCloning
open Occupation

theorem dimensionRatio_product (d n m : ℕ) (hd : 0 < d) :
    dimensionRatio d n m = ∏ i ∈ Finset.range (d - 1),
      ((n : ℝ) + i + 1) / (((n : ℝ) + i + 1) + m) := by
  rw [dimensionRatio, card_occupation_symm d n hd, card_occupation_symm d (n + m) hd,
    OccupationCounting.choose_add_eq_product, OccupationCounting.choose_add_eq_product,
    ← Finset.prod_div_distrib]
  apply Finset.prod_congr rfl
  intro i _
  rw [div_div_div_cancel_right₀ (by positivity : (i : ℝ) + 1 ≠ 0)]
  congr 1
  push_cast
  ring

/-- The rank-one cloning dimension loss, with the sharp number of active
roots d−1 rather than the number of all positive roots. -/
theorem dimensionRatio_loss_le (d n m : ℕ) (hd : 0 < d) :
    1 - dimensionRatio d n m ≤ ((d - 1 : ℕ) : ℝ) * m / ((n : ℝ) + 1) := by
  rw [dimensionRatio_product d n m hd]
  have h := Cloning.weyl_product_deficit_le_card (Finset.range (d - 1))
    (fun i => (n : ℝ) + i + 1) (fun _ => (m : ℝ)) (n : ℝ) (m : ℝ)
    (Nat.cast_nonneg n) (fun _ _ => by positivity)
    (fun i _ => Or.inr (by have := Nat.cast_nonneg (α := ℝ) i; linarith))
    (fun _ _ => Nat.cast_nonneg m) (fun _ _ => le_rfl)
  simpa only [Finset.card_range] using h

end FreeEntropy.OccupationCloning
