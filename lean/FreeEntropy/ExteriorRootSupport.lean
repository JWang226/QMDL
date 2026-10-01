/-
Copyright (c) 2026 Free Entropy formalization contributors.
See LICENSE and NOTICE in the repository root for license and attribution.
-/

import FreeEntropy.ExteriorSupportedMonomials

/-! Zero weight changes beyond the positive rank force every contributing
positive root to stay within that rank. This proves the support condition
needed for shallow multiplicities when the highest row has a zero tail. -/
noncomputable section
open scoped BigOperators
namespace FreeEntropy.ExteriorRepresentation
set_option backward.isDefEq.respectTransparency false
variable {d : ℕ}

theorem weighted_rootWeightShift (a : LowerRoot d →₀ ℕ) (f : Fin d → ℤ) :
    ∑ k, f k * rootWeightShift a k =
      ∑ r : LowerRoot d, (a r : ℤ) * (f r.val.2 - f r.val.1) := by
  simp only [rootWeightShift, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro r _
  simp only [mul_sub, mul_ite, mul_one, mul_zero, Finset.sum_sub_distrib]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
  ring

/-- A nonzero root coefficient cannot enter a tail whose coordinate
weight changes are all zero. -/
theorem root_target_lt_of_zero_tail (a : LowerRoot d →₀ ℕ) (rank : ℕ)
    (hzero : ∀ k : Fin d, rank ≤ k.val → rootWeightShift a k = 0)
    (r : LowerRoot d) (hr : a r ≠ 0) : r.val.2.val < rank := by
  classical
  let f : Fin d → ℤ := fun k => (k.val + 1 - rank : ℕ)
  have hf (s : LowerRoot d) : 0 ≤ f s.val.2 - f s.val.1 := by
    dsimp [f]
    have hs : s.val.1.val < s.val.2.val := s.property
    omega
  have hz : (∑ k, f k * rootWeightShift a k) = 0 := by
    apply Finset.sum_eq_zero
    intro k _
    by_cases hk : rank ≤ k.val
    · rw [hzero k hk, mul_zero]
    · have hfk : f k = 0 := by
        dsimp [f]
        have he : k.val + 1 - rank = 0 := by omega
        rw [he]
        rfl
      rw [hfk, zero_mul]
  rw [weighted_rootWeightShift] at hz
  have hle := Finset.single_le_sum (s := Finset.univ)
    (f := fun s : LowerRoot d => (a s : ℤ) * (f s.val.2 - f s.val.1))
    (fun s _ => mul_nonneg (Nat.cast_nonneg _) (hf s)) (Finset.mem_univ r)
  rw [hz] at hle
  have hpos : (0 : ℤ) < a r := by exact_mod_cast Nat.pos_of_ne_zero hr
  have hdiff : f r.val.2 - f r.val.1 ≤ 0 := by nlinarith [hf r]
  dsimp [f] at hdiff
  have hroot : r.val.1.val < r.val.2.val := r.property
  omega

/-- Rank support is inherited by every assignment in an equal-weight fiber. -/
theorem lowerWeightFiber_root_support (a b : LowerRoot d →₀ ℕ) (rank : ℕ)
    (hzero : ∀ k : Fin d, rank ≤ k.val → rootWeightShift a k = 0)
    (hb : b ∈ lowerWeightFiber a) (r : LowerRoot d) (hr : b r ≠ 0) :
    r.val.2.val < rank := by
  apply root_target_lt_of_zero_tail b rank _ r hr
  intro k hk
  rw [congrFun ((mem_lowerWeightFiber a b).mp hb) k]
  exact hzero k hk

end FreeEntropy.ExteriorRepresentation
