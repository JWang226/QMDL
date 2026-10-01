/-
Copyright (c) 2026 Free Entropy formalization contributors.
See LICENSE and NOTICE in the repository root for license and attribution.
-/

import FreeEntropy.LieMatrixCasimir

/-! The actual contragredient infinitesimal representation. -/
noncomputable section
open Matrix
namespace FreeEntropy.LieMatrixCasimir
variable {d : ℕ} {H : Type*} [Fintype H] [DecidableEq H]

/-- Dual coordinates act by the negative transpose of each generator. -/
def Generators.dual (R : Generators d H) : Generators d H where
  E i j := -(R.E i j)ᵀ
  adjoint := by
    intro i j
    rw [Matrix.conjTranspose_neg, Matrix.transpose_conjTranspose, ← Matrix.conjTranspose_transpose, R.adjoint]
  commutator := by
    intro i j k l
    have h := congrArg Matrix.transpose (R.commutator i j k l)
    simp only [Matrix.transpose_sub, Matrix.transpose_mul] at h
    simp only [neg_mul_neg]
    split_ifs at h ⊢ <;> simpa only [Matrix.transpose_zero, neg_sub,
      sub_zero, zero_sub, neg_neg, neg_sub_neg, neg_zero] using congrArg Neg.neg h

end FreeEntropy.LieMatrixCasimir
