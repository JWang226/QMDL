/-
Copyright (c) 2026 Free Entropy formalization contributors.
See LICENSE and NOTICE in the repository root for license and attribution.
-/

import FreeEntropy.WeylFinite
import Mathlib.Algebra.BigOperators.Fin

/-!
# Type-A root arithmetic behind the Casimir gap

Weights are actual real coordinate vectors; offsets are actual nonnegative
integer combinations of simple roots. The Casimir polynomial and all
pairings are defined explicitly. The representation theorem identifying
this polynomial with the Casimir eigenvalue remains separate.
-/

noncomputable section
open scoped BigOperators
namespace FreeEntropy.CasimirWeights

variable {d : ℕ}

def left (j : Fin (d - 1)) : Fin d := ⟨j.val, by omega⟩
def right (j : Fin (d - 1)) : Fin d := ⟨j.val + 1, by omega⟩

def simpleRoot (j : Fin (d - 1)) (i : Fin d) : ℝ :=
  (if i = left j then 1 else 0) - (if i = right j then 1 else 0)

def offset (c : Fin (d - 1) → ℕ) (i : Fin d) : ℝ :=
  ∑ j, (c j : ℝ) * simpleRoot j i

def depth (c : Fin (d - 1) → ℕ) : ℕ := ∑ j, c j

def dot (x y : Fin d → ℝ) : ℝ := ∑ i, x i * y i

def l1 (x : Fin d → ℝ) : ℝ := ∑ i, |x i|

def twiceRho (i : Fin d) : ℝ := (d : ℝ) - 1 - 2 * (i.val : ℝ)

def casimir (x : Fin d → ℝ) : ℝ := ∑ i, x i * (x i + twiceRho i)

theorem dot_simpleRoot (x : Fin d → ℝ) (j : Fin (d - 1)) :
    dot x (simpleRoot j) = x (left j) - x (right j) := by
  simp [dot, simpleRoot, mul_sub, Finset.sum_sub_distrib]

theorem dot_offset (x : Fin d → ℝ) (c : Fin (d - 1) → ℕ) :
    dot x (offset c) = ∑ j, (c j : ℝ) * (x (left j) - x (right j)) := by
  unfold dot offset
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  calc
    _ = (c j : ℝ) * dot x (simpleRoot j) := by
      simp only [dot, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ = _ := by rw [dot_simpleRoot]

theorem twiceRho_gap (j : Fin (d - 1)) : twiceRho (left j) - twiceRho (right j) = 2 := by
  simp [twiceRho, left, right, Nat.cast_add, Nat.cast_one]
  ring

/-- Exact Casimir eigenvalue difference written in simple-root coefficients. -/
theorem casimir_difference (ν χ : Fin d → ℝ) (c : Fin (d - 1) → ℕ)
    (hdiff : ν - χ = offset c) :
    casimir ν - casimir χ = ∑ j, (c j : ℝ) *
      ((ν (left j) - ν (right j)) + (χ (left j) - χ (right j)) + 2) := by
  have hid : casimir ν - casimir χ = dot (fun i => ν i + χ i + twiceRho i) (ν - χ) := by
    unfold casimir dot
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    simp only [Pi.sub_apply]
    ring
  rw [hid, hdiff, dot_offset]
  apply Finset.sum_congr rfl
  intro j _
  have hr := twiceRho_gap j
  congr 1
  linarith

/-- Supported adjacent row gaps and dominance give the linear Casimir gap. -/
theorem casimir_gap_times_depth (ν χ : Fin d → ℝ) (c : Fin (d - 1) → ℕ) (g : ℝ)
    (hdiff : ν - χ = offset c)
    (hν : ∀ j, c j ≠ 0 → g ≤ ν (left j) - ν (right j))
    (hχ : ∀ j, χ (right j) ≤ χ (left j)) :
    (g + 2) * (depth c : ℝ) ≤ casimir ν - casimir χ := by
  rw [casimir_difference ν χ c hdiff]
  unfold depth
  rw [Nat.cast_sum, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro j _
  by_cases hc : c j = 0
  · simp [hc]
  have h := mul_le_mul_of_nonneg_left (hν j hc) (Nat.cast_nonneg (c j) : (0 : ℝ) ≤ c j)
  have hχ' := mul_nonneg (Nat.cast_nonneg (c j) : (0 : ℝ) ≤ c j) (sub_nonneg.mpr (hχ j))
  nlinarith

/-- A nonzero integral offset has depth at least one, yielding the actual
`g+2` spectral separation used by the trace-deficit argument. -/
theorem casimir_gap (ν χ : Fin d → ℝ) (c : Fin (d - 1) → ℕ) (g : ℝ)
    (hg : 0 ≤ g) (hc : ∃ j, c j ≠ 0) (hdiff : ν - χ = offset c)
    (hν : ∀ j, c j ≠ 0 → g ≤ ν (left j) - ν (right j))
    (hχ : ∀ j, χ (right j) ≤ χ (left j)) :
    g + 2 ≤ casimir ν - casimir χ := by
  obtain ⟨j, hj⟩ := hc
  have hd : 1 ≤ depth c := (Nat.one_le_iff_ne_zero.mpr hj).trans
    (Finset.single_le_sum (fun i _ => Nat.zero_le _) (Finset.mem_univ j))
  have hdR : (1 : ℝ) ≤ (depth c : ℝ) := by exact_mod_cast hd
  have h := casimir_gap_times_depth ν χ c g hdiff hν hχ
  nlinarith

theorem coordinate_gap_le_l1 (x : Fin d → ℝ) (j : Fin (d - 1)) :
    x (left j) - x (right j) ≤ l1 x := by
  have hne : left j ≠ right j := by
    intro h
    have hv := congrArg Fin.val h
    simp [left, right] at hv
  have hs : ({left j, right j} : Finset (Fin d)) ⊆ Finset.univ := Finset.subset_univ _
  have hsum := Finset.sum_le_sum_of_subset_of_nonneg hs (fun i _ _ => abs_nonneg (x i))
  have hpair : (∑ i ∈ ({left j, right j} : Finset (Fin d)), |x i|) =
      |x (left j)| + |x (right j)| := by simp [hne]
  rw [hpair] at hsum
  unfold l1
  linarith [le_abs_self (x (left j)), neg_le_abs (x (right j))]

/-- The dot product of a positive-root offset with a dominant increment
lies between zero and depth times the coordinate L1 norm. -/
theorem offset_dot_bounds (c : Fin (d - 1) → ℕ) (ω : Fin d → ℝ)
    (hω : ∀ j, ω (right j) ≤ ω (left j)) :
    0 ≤ dot ω (offset c) ∧ dot ω (offset c) ≤ (depth c : ℝ) * l1 ω := by
  rw [dot_offset]
  constructor
  · exact Finset.sum_nonneg fun j _ => mul_nonneg (Nat.cast_nonneg _) (sub_nonneg.mpr (hω j))
  · calc
      _ ≤ ∑ j, (c j : ℝ) * l1 ω := Finset.sum_le_sum fun j _ =>
        mul_le_mul_of_nonneg_left (coordinate_gap_le_l1 ω j) (Nat.cast_nonneg _)
      _ = _ := by rw [← Finset.sum_mul, ← Nat.cast_sum]; rfl

/-- Additivity of the explicit Casimir polynomial up to its cross term. -/
theorem casimir_add (μ ω : Fin d → ℝ) :
    casimir (μ + ω) = casimir μ + casimir ω + 2 * dot μ ω := by
  unfold casimir dot
  rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  simp only [Pi.add_apply]
  ring

/-- The numerical cancellation after compressing the tensor-product
Casimir: the remaining deficit is exactly twice the offset pairing. -/
theorem casimir_deficit (μ ω δ : Fin d → ℝ) :
    casimir (μ + ω) - casimir μ - casimir ω - 2 * dot (μ - δ) ω = 2 * dot δ ω := by
  rw [casimir_add]
  have hd : dot (μ - δ) ω = dot μ ω - dot δ ω := by
    simp [dot, sub_mul, Finset.sum_sub_distrib]
  rw [hd]
  ring

/-- The exact compressed Casimir polynomial has the required nonnegative
`2 · depth · L1` deficit bound. Only its representation-theoretic identification
with the compressed operator remains to be supplied. -/
theorem casimir_deficit_bounds (μ ω : Fin d → ℝ) (c : Fin (d - 1) → ℕ)
    (hω : ∀ j, ω (right j) ≤ ω (left j)) :
    0 ≤ casimir (μ + ω) - casimir μ - casimir ω - 2 * dot (μ - offset c) ω ∧
      casimir (μ + ω) - casimir μ - casimir ω - 2 * dot (μ - offset c) ω ≤
        2 * (depth c : ℝ) * l1 ω := by
  rw [casimir_deficit]
  have he : dot (offset c) ω = dot ω (offset c) := by
    unfold dot
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [he]
  have h := offset_dot_bounds c ω hω
  constructor <;> nlinarith

end FreeEntropy.CasimirWeights
