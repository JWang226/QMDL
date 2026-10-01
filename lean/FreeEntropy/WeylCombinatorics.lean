/-
Copyright (c) 2026 Free Entropy formalization contributors.
See LICENSE and NOTICE in the repository root for license and attribution.
-/

import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Data.Nat.Factorial.BigOperators
import Mathlib.Tactic.Linarith
import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.Ring
import FreeEntropy.Weyl

/-! Elementary counting and denominator identities for the active Weyl roots.
The identities include the zero-rank and zero-dimension empty products. -/

namespace FreeEntropy.Weyl

open scoped BigOperators

/-- Twice the number of active roots, with no rounding in the coefficient. -/
theorem twice_active_row_count (d r : ℕ) (hr : r ≤ d) :
    2 * (∑ i ∈ Finset.range r, (d - i - 1)) = r * (2 * d - r - 1) := by
  by_cases hr0 : r = 0
  · simp [hr0]
  have hsum : (∑ i ∈ Finset.range r, (d - i - 1)) +
      (∑ i ∈ Finset.range r, (i + 1)) = r * d := by
    rw [← Finset.sum_add_distrib]
    calc
      (∑ i ∈ Finset.range r, (d - i - 1 + (i + 1))) =
          ∑ _i ∈ Finset.range r, d := by
        apply Finset.sum_congr rfl
        intro i hi
        have hi' := Finset.mem_range.mp hi
        omega
      _ = r * d := by simp
  have hseries := Finset.sum_range_id_mul_two r
  have hsum_succ : (∑ i ∈ Finset.range r, (i + 1)) =
      (∑ i ∈ Finset.range r, i) + r := by simp [Finset.sum_add_distrib]
  rw [hsum_succ] at hsum
  have hrsub : r - 1 + 1 = r := by omega
  have hdsub : 2 * d - r - 1 + r + 1 = 2 * d := by omega
  nlinarith

/-- The active-root coefficient in the precise form printed in Theorem 1. -/
theorem active_row_count (d r : ℕ) (hr : r ≤ d) :
    (∑ i ∈ Finset.range r, (d - i - 1)) = r * (2 * d - r - 1) / 2 := by
  have h := congrArg (fun k : ℕ => k / 2) (twice_active_row_count d r hr)
  simpa using h

/-- The denominator factors in one row form a factorial. -/
theorem row_denominator (d i : ℕ) :
    (∏ j ∈ Finset.Ico (i + 1) d, (j - i)) = (d - i - 1).factorial := by
  rw [Finset.prod_Ico_eq_prod_range]
  calc
    (∏ k ∈ Finset.range (d - (i + 1)), (i + 1 + k - i)) =
        ∏ k ∈ Finset.range (d - (i + 1)), (k + 1) := by
      apply Finset.prod_congr rfl
      intro k _
      omega
    _ = (d - i - 1).factorial := by
      rw [Finset.prod_range_add_one_eq_factorial]
      congr 1

/-- Reversing the row order produces the consecutive factorials in the paper. -/
theorem descending_factorial_product (d r : ℕ) (hr : r ≤ d) :
    (∏ i ∈ Finset.range r, (d - i - 1).factorial) =
      ∏ k ∈ Finset.Ico (d - r) d, k.factorial := by
  by_cases hd0 : d = 0
  · have hr0 : r = 0 := by omega
    simp [hd0, hr0]
  have hreflect := Finset.prod_Ico_reflect Nat.factorial 0
    (m := r) (n := d - 1) (by omega)
  have hd : d - 1 + 1 = d := by omega
  rw [hd, Nat.sub_zero, Nat.Ico_zero_eq_range] at hreflect
  rw [← hreflect]
  apply Finset.prod_congr rfl
  intro i _
  congr 1
  omega

/-- Exact cancellation denominator for the rank-r Weyl dimension formula. -/
theorem active_denominator (d r : ℕ) (hr : r ≤ d) :
    (∏ i ∈ Finset.range r, ∏ j ∈ Finset.Ico (i + 1) d, (j - i)) =
      ∏ k ∈ Finset.Ico (d - r) d, k.factorial := by
  simp_rw [row_denominator]
  exact descending_factorial_product d r hr

theorem activeRoots_rows_disjoint (d r : ℕ) :
    Set.PairwiseDisjoint (↑(Finset.range r) : Set ℕ)
      (fun i => (Finset.Ico (i + 1) d).image (fun j => (i, j))) := by
  intro i _ j _ hij
  apply Finset.disjoint_left.mpr
  intro p hp hq
  obtain ⟨a, _, ha⟩ := Finset.mem_image.mp hp
  obtain ⟨b, _, hb⟩ := Finset.mem_image.mp hq
  have heq : i = j := congrArg Prod.fst (ha.trans hb.symm)
  exact hij heq

/-- Expand a root-indexed sum into rows without counting a root twice. -/
theorem sum_activeRoots {M : Type*} [AddCommMonoid M] (d r : ℕ)
    (f : ℕ × ℕ → M) :
    (∑ p ∈ activeRoots d r, f p) =
      ∑ i ∈ Finset.range r, ∑ j ∈ Finset.Ico (i + 1) d, f (i, j) := by
  rw [activeRoots, Finset.sum_biUnion (activeRoots_rows_disjoint d r)]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_image]
  intro a _ b _ h
  exact (Prod.mk.inj h).2

/-- Exact active-root cardinality. -/
theorem card_activeRoots (d r : ℕ) (hr : r ≤ d) :
    (activeRoots d r).card = r * (2 * d - r - 1) / 2 := by
  have h := sum_activeRoots d r (fun _ => (1 : ℕ))
  simp only [Finset.sum_const, smul_eq_mul, mul_one, Nat.card_Ico] at h
  rw [h]
  convert active_row_count d r hr using 2

/-- The cardinality written with real arithmetic, as in the manuscript. -/
theorem card_activeRoots_real (d r : ℕ) (hr : r ≤ d) :
    ((activeRoots d r).card : ℝ) =
      (r : ℝ) * (2 * (d : ℝ) - (r : ℝ) - 1) / 2 := by
  have hsum := sum_activeRoots d r (fun _ => (1 : ℕ))
  simp only [Finset.sum_const, smul_eq_mul, mul_one, Nat.card_Ico] at hsum
  have hc : (activeRoots d r).card = ∑ i ∈ Finset.range r, (d - i - 1) := by
    rw [hsum]
    apply Finset.sum_congr rfl
    intro i _
    omega
  rw [hc]
  by_cases hr0 : r = 0
  · simp [hr0]
  have hcount : 2 * ((∑ i ∈ Finset.range r, (d - i - 1) : ℕ) : ℝ) =
      (r : ℝ) * ((2 * d - r - 1 : ℕ) : ℝ) := by
    exact_mod_cast twice_active_row_count d r hr
  have hdsub : ((2 * d - r - 1 : ℕ) : ℝ) + (r : ℝ) + 1 = 2 * (d : ℝ) := by
    have hh : 2 * d - r - 1 + r + 1 = 2 * d := by omega
    exact_mod_cast hh
  nlinarith

/-- An additive version of reversing the factorial denominator's row order. -/
theorem descending_row_sum (d r : ℕ) (hr : r ≤ d) (f : ℕ → ℝ) :
    (∑ i ∈ Finset.range r, f (d - i - 1)) =
      ∑ k ∈ Finset.Ico (d - r) d, f k := by
  by_cases hd0 : d = 0
  · have hr0 : r = 0 := by omega
    simp [hd0, hr0]
  have hreflect := Finset.sum_Ico_reflect f 0
    (m := r) (n := d - 1) (by omega)
  have hd : d - 1 + 1 = d := by omega
  rw [hd, Nat.sub_zero, Nat.Ico_zero_eq_range] at hreflect
  rw [← hreflect]
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  omega

/-- The logarithmic denominator of a single active row. -/
theorem log_row_denominator (d i : ℕ) :
    (∑ j ∈ Finset.Ico (i + 1) d, Real.logb 2 ((j - i : ℕ) : ℝ)) =
      Real.logb 2 ((d - i - 1).factorial : ℝ) := by
  rw [← row_denominator d i, Nat.cast_prod, Real.logb_prod]
  intro j hj
  have hij := (Finset.mem_Ico.mp hj).1
  have hpos : 0 < j - i := by omega
  exact_mod_cast hpos.ne'

/-- The full base-two logarithmic denominator. -/
theorem log_active_denominator (d r : ℕ) (hr : r ≤ d) :
    (∑ i ∈ Finset.range r,
      ∑ j ∈ Finset.Ico (i + 1) d, Real.logb 2 ((j - i : ℕ) : ℝ)) =
      ∑ k ∈ Finset.Ico (d - r) d, Real.logb 2 (k.factorial : ℝ) := by
  simp_rw [log_row_denominator]
  exact descending_row_sum d r hr (fun k => Real.logb 2 (k.factorial : ℝ))

/-- The explicit expression `L_{d,r}(n,x)` in Theorem 1, with zero-based
indices, real arithmetic in the coefficient, and base-two logarithms. -/
noncomputable def qmdl (d r : ℕ) (x : ℕ → ℝ) (n : ℕ) : ℝ :=
  (r : ℝ) * (2 * (d : ℝ) - (r : ℝ) - 1) / 2 * Real.logb 2 n +
    (∑ i ∈ Finset.range r, ∑ j ∈ Finset.Ico (i + 1) r,
      Real.logb 2 (x i - x j)) +
    ((d - r : ℕ) : ℝ) * (∑ i ∈ Finset.range r, Real.logb 2 (x i)) -
    ∑ k ∈ Finset.Ico (d - r) d, Real.logb 2 (k.factorial : ℝ)

/-- Splitting positive-positive from positive-zero roots produces the two
spectral sums in the manuscript. -/
theorem spectral_sum_split (d r : ℕ) (hr : r ≤ d) (x : ℕ → ℝ)
    (hzero : ∀ j, r ≤ j → j < d → x j = 0) :
    (∑ i ∈ Finset.range r, ∑ j ∈ Finset.Ico (i + 1) d,
      Real.logb 2 (x i - x j)) =
    (∑ i ∈ Finset.range r, ∑ j ∈ Finset.Ico (i + 1) r,
      Real.logb 2 (x i - x j)) +
    ((d - r : ℕ) : ℝ) * (∑ i ∈ Finset.range r, Real.logb 2 (x i)) := by
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  have hir : i + 1 ≤ r := Nat.succ_le_of_lt (Finset.mem_range.mp hi)
  rw [← Finset.sum_Ico_consecutive (fun j => Real.logb 2 (x i - x j)) hir hr]
  congr 1
  calc
    (∑ j ∈ Finset.Ico r d, Real.logb 2 (x i - x j)) =
        ∑ _j ∈ Finset.Ico r d, Real.logb 2 (x i) := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [hzero j (Finset.mem_Ico.mp hj).1 (Finset.mem_Ico.mp hj).2, sub_zero]
    _ = ((d - r : ℕ) : ℝ) * Real.logb 2 (x i) := by simp

/-- The analytic root expression is exactly the displayed formula of
Theorem 1; no additive constant is discarded. -/
theorem rootLeading_eq_qmdl (d r : ℕ) (hr : r ≤ d) (x : ℕ → ℝ) (n : ℕ)
    (hgap : ∀ i j, i < r → i < j → j < d → x j < x i)
    (hzero : ∀ j, r ≤ j → j < d → x j = 0) :
    rootLeading d r x n = qmdl d r x n := by
  unfold rootLeading qmdl
  rw [card_activeRoots_real d r hr, sum_activeRoots]
  have hlogs :
      (∑ i ∈ Finset.range r, ∑ j ∈ Finset.Ico (i + 1) d,
        Real.logb 2 ((x i - x j) / ((j - i : ℕ) : ℝ))) =
      (∑ i ∈ Finset.range r, ∑ j ∈ Finset.Ico (i + 1) d,
        Real.logb 2 (x i - x j)) -
      (∑ i ∈ Finset.range r, ∑ j ∈ Finset.Ico (i + 1) d,
        Real.logb 2 ((j - i : ℕ) : ℝ)) := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro j hj
    have hij : i < j := by have := (Finset.mem_Ico.mp hj).1; omega
    apply Real.logb_div
    · exact (sub_pos.mpr (hgap i j (Finset.mem_range.mp hi) hij
        (Finset.mem_Ico.mp hj).2)).ne'
    · exact_mod_cast (Nat.sub_pos_of_lt hij).ne'
  dsimp only [Prod.fst, Prod.snd]
  rw [hlogs, log_active_denominator d r hr, spectral_sum_split d r hr x hzero]
  ring

end FreeEntropy.Weyl
