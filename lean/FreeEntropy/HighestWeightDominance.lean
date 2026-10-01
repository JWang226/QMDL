/-
Copyright (c) 2026 Free Entropy formalization contributors.
See LICENSE and NOTICE in the repository root for license and attribution.
-/

import FreeEntropy.LieMatrixCasimir

/-! Dominance of a genuine highest weight follows from positivity and the
matrix Lie relations. It is not a separate hypothesis on the representation. -/
noncomputable section
open Matrix
open scoped ComplexOrder
namespace FreeEntropy.LieMatrixCasimir
set_option backward.isDefEq.respectTransparency false
variable {d : ℕ} {H : Type*} [Fintype H] [DecidableEq H]

/-- Applying a matrix unit shifts the joint weight by its actual root. -/
theorem Generators.raising_weight (R : Generators d H) (lam : Fin d → ℂ)
    (v : H → ℂ) (hweight : ∀ k, R.E k k *ᵥ v = lam k • v) (i j k : Fin d) :
    R.E k k *ᵥ (R.E i j *ᵥ v) =
      (lam k + (if k = i then 1 else 0) - (if k = j then 1 else 0)) • (R.E i j *ᵥ v) := by
  have hc : R.E k k * R.E i j - R.E i j * R.E k k =
      ((if k = i then 1 else 0 : ℂ) - (if k = j then 1 else 0)) • R.E i j := by
    rw [R.commutator]
    by_cases hki : k = i <;> by_cases hkj : k = j
    · subst i; subst j; simp
    · subst i; simp [hkj, Ne.symm hkj]
    · subst j; simp [hki]
    · simp [hki, hkj, Ne.symm hkj]
  have hv := congrArg (fun M : Matrix H H ℂ => M *ᵥ v) hc
  simp only [Matrix.sub_mulVec, ← Matrix.mulVec_mulVec, hweight,
    Matrix.mulVec_smul, Matrix.smul_mulVec] at hv
  rw [sub_eq_iff_eq_add] at hv
  rw [hv]
  module

theorem Generators.highest_weight_dominant (R : Generators d H)
    (lam : Fin d → ℝ) (v : H → ℂ) (hv : v ≠ 0)
    (hweight : ∀ i, R.E i i *ᵥ v = lam i • v)
    (hraise : ∀ i j, i < j → R.E i j *ᵥ v = 0) : Antitone lam := by
  intro i j hij
  rcases eq_or_lt_of_le hij with rfl | hlt
  · exact le_rfl
  have hzero : (R.E j i * R.E i j) *ᵥ v = 0 := by
    rw [← Matrix.mulVec_mulVec, hraise i j hlt, Matrix.mulVec_zero]
  have he := congrArg (fun M : Matrix H H ℂ => M *ᵥ v) (R.commutator i j j i)
  simp only [if_true, Matrix.sub_mulVec, hzero, sub_zero, hweight, ← sub_smul] at he
  have hpos : (R.E i j * R.E j i).PosSemidef := by
    rw [← R.adjoint i j]
    exact Matrix.posSemidef_self_mul_conjTranspose _
  have hn := (RCLike.nonneg_iff.mp (hpos.dotProduct_mulVec_nonneg v)).1
  rw [he, dotProduct_smul] at hn
  have hvpos : 0 < (star v ⬝ᵥ v).re :=
    (RCLike.pos_iff.mp (dotProduct_star_self_pos_iff.mpr hv)).1
  have hn' : 0 ≤ (lam i - lam j) * (star v ⬝ᵥ v).re := by
    change 0 ≤ ((lam i - lam j : ℝ) • (star v ⬝ᵥ v)).re at hn
    simpa using hn
  nlinarith

end FreeEntropy.LieMatrixCasimir
