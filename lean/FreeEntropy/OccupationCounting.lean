/-
Copyright (c) 2026 Free Entropy formalization contributors.
See LICENSE and NOTICE in the repository root for license and attribution.
-/

import FreeEntropy.GTDimensionFormula
import Mathlib.Algebra.Order.Antidiag.FinsuppEquiv
import Mathlib.Data.Nat.Factorial.BigOperators

/-! Exact composition counts and their logarithmic asymptotic. -/

noncomputable section
open Filter
open scoped BigOperators Topology

namespace FreeEntropy.OccupationCounting

/-- Explicit identification of finite compositions with supported natural
assignments, allowing the library's proved stars-and-bars theorem to apply. -/
def compositionEquivAntidiag (d n : ℕ) :
    {lam : Fin d → ℕ // ∑ i, lam i = n} ≃
      ((Finset.univ : Finset (Fin d)).finsuppAntidiag n) where
  toFun lam := ⟨Finsupp.equivFunOnFinite.symm lam.val, by
    apply Finset.mem_finsuppAntidiag.mpr
    exact ⟨by simpa using lam.property, Finset.subset_univ _⟩⟩
  invFun c := ⟨c.val, (Finset.mem_finsuppAntidiag.mp c.property).1⟩
  left_inv lam := by apply Subtype.ext; rfl
  right_inv c := by apply Subtype.ext; exact Finsupp.equivFunOnFinite.symm_apply_apply c.val

theorem card_compositions (d n : ℕ) :
    Nat.card {lam : Fin d → ℕ // ∑ i, lam i = n} = (d + n - 1).choose n := by
  rw [Nat.card_congr (compositionEquivAntidiag d n), Nat.card_eq_fintype_card,
    Fintype.card_coe, Finset.card_finsuppAntidiag_nat_eq_choose]
  simp

theorem card_compositions_symm (d n : ℕ) (hd : 0 < d) :
    Nat.card {lam : Fin d → ℕ // ∑ i, lam i = n} = (n + (d - 1)).choose (d - 1) := by
  rw [card_compositions, show d + n - 1 = n + (d - 1) by omega]
  exact Nat.choose_symm_add

theorem choose_add_eq_product (n k : ℕ) :
    ((n + k).choose k : ℝ) =
      ∏ i ∈ Finset.range k, (((n : ℝ) + i + 1) / ((i : ℝ) + 1)) := by
  rw [Finset.prod_div_distrib]
  have hn : (∏ i ∈ Finset.range k, ((n : ℝ) + i + 1)) =
      ((n + 1).ascFactorial k : ℝ) := by
    rw [Nat.ascFactorial_eq_prod_range, Nat.cast_prod]
    apply Finset.prod_congr rfl
    intro i _
    push_cast
    ring
  have hk : (∏ i ∈ Finset.range k, ((i : ℝ) + 1)) = (k.factorial : ℝ) := by
    exact_mod_cast (Nat.factorial_eq_prod_range_add_one k).symm
  rw [hn, hk, Nat.ascFactorial_eq_factorial_mul_choose, Nat.cast_mul]
  exact (mul_div_cancel_left₀ _ (by exact_mod_cast k.factorial_ne_zero)).symm

theorem choose_log_asymptotic (k : ℕ) :
    Tendsto (fun n : ℕ => Real.logb 2 ((n + k).choose k) -
      ((k : ℝ) * Real.logb 2 n - Real.logb 2 (k.factorial : ℝ))) atTop (𝓝 0) := by
  have h := Weyl.log_product_asymptotic (Finset.range k)
    (fun n i => ((n : ℝ) + i + 1) / ((i : ℝ) + 1))
    (fun i => 1 / ((i : ℝ) + 1))
    (fun i _ => by positivity) (fun i _ => by
      have hc : Tendsto (fun n : ℕ => ((i : ℝ) + 1) / (n : ℝ)) atTop (𝓝 0) :=
        tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
      have h1 : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1) := tendsto_const_nhds
      have hh := (h1.add hc).div_const ((i : ℝ) + 1)
      simp only [add_zero] at hh
      apply hh.congr'
      filter_upwards [eventually_ge_atTop 1] with n hn
      have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
      have hi0 : (i : ℝ) + 1 ≠ 0 := by positivity
      field_simp
      ring)
  have hs : (∑ i ∈ Finset.range k, Real.logb 2 (1 / ((i : ℝ) + 1))) =
      -Real.logb 2 (k.factorial : ℝ) := by
    rw [← Real.logb_prod (Finset.range k) (fun i => 1 / ((i : ℝ) + 1))
      (fun i _ => by positivity), Finset.prod_div_distrib]
    have hk : (∏ i ∈ Finset.range k, ((i : ℝ) + 1)) = (k.factorial : ℝ) := by
      exact_mod_cast (Nat.factorial_eq_prod_range_add_one k).symm
    simp only [Finset.prod_const_one, hk, one_div, Real.logb_inv]
  simpa only [← choose_add_eq_product, Finset.card_range, hs, sub_eq_add_neg] using h

theorem qmdl_rank_one (d n : ℕ) (hd : 0 < d) (x : ℕ → ℝ) (hx : x 0 = 1) :
    Weyl.qmdl d 1 x n =
      ((d - 1 : ℕ) : ℝ) * Real.logb 2 n - Real.logb 2 ((d - 1).factorial : ℝ) := by
  have hcast : ((d - 1 : ℕ) : ℝ) = (d : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ d)]; norm_num
  unfold Weyl.qmdl
  simp only [Nat.cast_one, Finset.sum_range_succ, Finset.sum_range_zero,
    zero_add, Finset.Ico_self, Finset.sum_empty, hx, Real.logb_one, mul_zero,
    add_zero]
  have hi : Finset.Ico (d - 1) d = {d - 1} := Nat.Ico_pred_singleton hd
  rw [hi, Finset.sum_singleton, hcast]
  ring

end FreeEntropy.OccupationCounting
