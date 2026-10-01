/-
Copyright (c) 2026 Free Entropy formalization contributors.
See LICENSE and NOTICE in the repository root for license and attribution.
-/

import FreeEntropy.GTDimension
import FreeEntropy.GTDeterminant

/-!
# The binomial determinant counts actual GT patterns

An explicit reversal-and-shift equivalence identifies interlacing rows with
the independent half-open intervals of the determinant recurrence. Induction
on the number of rows therefore proves the determinant enumeration of the
actual finite type `GelfandTsetlin.Pattern μ`.
-/

noncomputable section
open scoped BigOperators

namespace FreeEntropy.GTDimension

open GelfandTsetlin

def interlacingToInterval {n : ℕ} (μ : Fin (n + 1) → ℤ) (ν : InterlacingRow μ) :
    IntervalRows (shiftedRow μ) := fun i =>
  ⟨interlacingWeight ν i.rev + i.val, by
    have hl := interlacingWeight_lower ν i.rev
    have hu := interlacingWeight_upper ν i.rev
    apply Finset.mem_Ico.mpr
    simp only [shiftedRow, Fin.rev_castSucc, Fin.rev_succ, Fin.val_castSucc, Fin.val_succ]
    omega⟩

def intervalToInterlacing {n : ℕ} (μ : Fin (n + 1) → ℤ)
    (z : IntervalRows (shiftedRow μ)) : InterlacingRow μ := fun i =>
  ⟨(z i.rev).val - i.rev.val, by
    have h := Finset.mem_Ico.mp (z i.rev).property
    simp only [shiftedRow, Fin.rev_castSucc, Fin.rev_succ, Fin.rev_rev,
      Fin.val_castSucc, Fin.val_succ] at h
    apply Finset.mem_Icc.mpr
    omega⟩

/-- Reversing and shifting the interlacing coordinates turns closed
interlacing intervals into independent strictly ordered half-open intervals. -/
def interlacingIntervalEquiv {n : ℕ} (μ : Fin (n + 1) → ℤ) :
    InterlacingRow μ ≃ IntervalRows (shiftedRow μ) where
  toFun := interlacingToInterval μ
  invFun := intervalToInterlacing μ
  left_inv ν := by
    funext i
    apply Subtype.ext
    simp [intervalToInterlacing, interlacingToInterval, interlacingWeight, Fin.rev_rev]
    exact congrArg (fun j : Fin n => (ν j).val) (Fin.rev_rev i)
  right_inv z := by
    funext i
    apply Subtype.ext
    simp [intervalToInterlacing, interlacingToInterval, interlacingWeight, Fin.rev_rev]
    exact congrArg (fun j : Fin n => (z j).val) (Fin.rev_rev i)

theorem shiftedRow_adjacent {n : ℕ} {μ : Fin (n + 1) → ℤ} (hμ : Dominant μ)
    (i : Fin n) : shiftedRow μ i.castSucc ≤ shiftedRow μ i.succ := by
  have h : μ i.rev.succ ≤ μ i.rev.castSucc :=
    hμ (by change i.rev.val ≤ i.rev.val + 1; omega)
  simp only [shiftedRow, Fin.rev_castSucc, Fin.rev_succ, Fin.val_castSucc, Fin.val_succ]
  omega

/-- The determinant satisfies precisely the proved GT branching recurrence. -/
theorem binomialDet_branching {n : ℕ} (μ : Fin (n + 1) → ℤ) (hμ : Dominant μ) :
    binomialDet μ = ∑ ν : InterlacingRow μ, binomialDet (interlacingWeight ν) := by
  rw [binomialDet, chooseDet_interval_sum _ (shiftedRow_adjacent hμ)]
  rw [← (interlacingIntervalEquiv μ).sum_comp (fun z => chooseDet (fun i => (z i).val))]
  rfl

/-- The all-dimension binomial determinant formula for actual integral GT patterns. -/
theorem card_eq_binomialDet {n : ℕ} (μ : Fin n → ℤ) (hμ : Dominant μ) :
    (Fintype.card (Pattern μ) : ℝ) = binomialDet μ := by
  induction n with
  | zero =>
    rw [card_zero]
    simp [binomialDet, chooseDet]
  | succ n ih =>
    rw [card_branching, Nat.cast_sum, binomialDet_branching μ hμ]
    apply Finset.sum_congr rfl
    intro ν _
    exact ih (interlacingWeight ν) (interlacingWeight_dominant hμ ν)

end FreeEntropy.GTDimension
