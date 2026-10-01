/-
Copyright (c) 2026 Free Entropy formalization contributors.
See LICENSE and NOTICE in the repository root for license and attribution.
-/

import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.RingTheory.Binomial
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Data.Int.Interval
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

/-! Binomial determinants and their finite interlacing recurrence. These
identities supply the enumeration side of the actual GT dimension formula. -/
noncomputable section
open scoped BigOperators
open Matrix
namespace FreeEntropy.GTDimension
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false

/-- Binomial evaluation determinant on an increasing integral row. -/
def chooseDet {n : ℕ} (x : Fin n → ℤ) : ℝ :=
  Matrix.det (fun i j : Fin n => Ring.choose (x i : ℝ) j.val)

/-- Reverse and shift a dominant row into strictly increasing coordinates. -/
def shiftedRow {n : ℕ} (μ : Fin n → ℤ) (i : Fin n) : ℤ := μ i.rev + i.val

def binomialDet {n : ℕ} (μ : Fin n → ℤ) : ℝ := chooseDet (shiftedRow μ)

/-- Discrete integration of the binomial polynomials, including negative endpoints. -/
theorem sum_choose_Ico (a b : ℤ) (hab : a ≤ b) (k : ℕ) :
    (∑ z ∈ Finset.Ico a b, Ring.choose (z : ℝ) k) =
      Ring.choose (b : ℝ) (k + 1) - Ring.choose (a : ℝ) (k + 1) := by
  rw [Int.Ico_eq_finset_map, Finset.sum_map]
  let f : ℕ → ℝ := fun j => Ring.choose ((a : ℝ) + j) (k + 1)
  have ht (j : ℕ) : Ring.choose ((a : ℝ) + j) k = f (j + 1) - f j := by
    dsimp [f]
    rw [Nat.cast_add, Nat.cast_one, ← add_assoc, Ring.choose_succ_succ]
    ring
  simp only [Function.Embedding.trans_apply, Nat.castEmbedding_apply, addLeftEmbedding_apply,
    Int.cast_add, Int.cast_natCast]
  simp_rw [ht]
  rw [Finset.sum_range_sub]
  have hend : (a : ℝ) + ((b - a).toNat : ℝ) = b := by
    have hi := Int.toNat_of_nonneg (sub_nonneg.mpr hab)
    have hr : ((b - a).toNat : ℝ) = (b : ℝ) - a := by exact_mod_cast hi
    linarith
  simp [f, hend]

/-- Independently choosing an integer in each successive half-open interval. -/
abbrev IntervalRows {n : ℕ} (x : Fin (n + 1) → ℤ) :=
  (i : Fin n) → {z : ℤ // z ∈ Finset.Ico (x i.castSucc) (x i.succ)}

/-- Subtracting each preceding row leaves the finite-difference determinant. -/
theorem chooseDet_difference {n : ℕ} (x : Fin (n + 1) → ℤ) :
    chooseDet x = Matrix.det (fun i j : Fin n =>
      Ring.choose (x i.succ : ℝ) (j.val + 1) -
        Ring.choose (x i.castSucc : ℝ) (j.val + 1)) := by
  let A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ :=
    fun i j => Ring.choose (x i : ℝ) j.val
  let B : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ :=
    Fin.cases (A 0) (fun i => A i.succ - A i.castSucc)
  have hdet : A.det = B.det := Matrix.det_eq_of_forall_row_eq_smul_add_pred
    (fun _ => 1) (fun _ => rfl) (fun i j => by simp [B])
  change A.det = _
  rw [hdet, Matrix.det_succ_column_zero]
  rw [Finset.sum_eq_single 0]
  · simp only [Fin.val_zero, pow_zero, one_mul, Fin.succAbove_zero]
    have hb : B 0 0 = 1 := by simp [B, A]
    rw [hb, one_mul]
    rfl
  · intro i _ hi
    have hb : B i 0 = 0 := by
      obtain ⟨i, rfl⟩ := Fin.eq_succ_of_ne_zero hi
      simp [B, A]
    rw [hb, mul_zero, zero_mul]
  · simp

/-- The exact branching recurrence for binomial determinants. -/
theorem chooseDet_interval_sum {n : ℕ} (x : Fin (n + 1) → ℤ)
    (hx : ∀ i : Fin n, x i.castSucc ≤ x i.succ) :
    chooseDet x = ∑ z : IntervalRows x, chooseDet (fun i => (z i).val) := by
  have h := (Matrix.detRowAlternating (n := Fin n) (R := ℝ)).toMultilinearMap.map_sum
    (fun i (z : {z : ℤ // z ∈ Finset.Ico (x i.castSucc) (x i.succ)})
      (j : Fin n) => Ring.choose (z.val : ℝ) j.val)
  have hs (i j : Fin n) :
      (∑ z : {z : ℤ // z ∈ Finset.Ico (x i.castSucc) (x i.succ)},
        Ring.choose (z.val : ℝ) j.val) =
        Ring.choose (x i.succ : ℝ) (j.val + 1) -
          Ring.choose (x i.castSucc : ℝ) (j.val + 1) := by
    rw [Finset.sum_coe_sort (Finset.Ico (x i.castSucc) (x i.succ))
      (fun z : ℤ => Ring.choose (z : ℝ) j.val)]
    exact sum_choose_Ico _ _ (hx i) j.val
  rw [chooseDet_difference]
  calc
    _ = Matrix.det (fun i : Fin n => ∑ z : {z : ℤ // z ∈ Finset.Ico (x i.castSucc) (x i.succ)},
        fun j : Fin n => Ring.choose (z.val : ℝ) j.val) := by
      congr 1
      funext i j
      simp only [Finset.sum_apply]
      exact (hs i j).symm
    _ = _ := h

/-- The exact Vandermonde product formula for the binomial determinant. -/
theorem chooseDet_product {n : ℕ} (x : Fin n → ℤ) :
    chooseDet x = (∏ i : Fin n, ∏ j ∈ Finset.Ioi i, ((x j : ℝ) - x i)) /
      ∏ j : Fin n, (j.val.factorial : ℝ) := by
  have hev (y : ℝ) (k : ℕ) :
      (descPochhammer ℝ k).eval y = (k.factorial : ℝ) * Ring.choose y k := by
    have h := Ring.descPochhammer_eq_factorial_smul_choose y k
    rw [← Polynomial.eval₂_smulOneHom_eq_smeval, Polynomial.eval₂_eq_eval_map,
      descPochhammer_map, nsmul_eq_mul] at h
    exact h
  have h := Matrix.det_eval_matrixOfPolynomials_eq_det_vandermonde
    (fun i => (x i : ℝ)) (fun j : Fin n => descPochhammer ℝ j.val)
    (fun j => descPochhammer_natDegree ℝ j.val) (fun j => monic_descPochhammer ℝ j.val)
  simp only [hev] at h
  rw [Matrix.det_mul_row, Matrix.det_vandermonde] at h
  apply (eq_div_iff (Finset.prod_ne_zero_iff.mpr (fun j _ => by positivity))).2
  simpa [chooseDet, mul_comm] using h.symm

end FreeEntropy.GTDimension
