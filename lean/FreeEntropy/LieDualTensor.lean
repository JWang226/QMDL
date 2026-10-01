/-
Copyright (c) 2026 Free Entropy formalization contributors.
See LICENSE and NOTICE in the repository root for license and attribution.
-/

import FreeEntropy.CartanReshuffle

/-! Contragredient and tensor-swap operations on actual Lie intertwiners. -/
noncomputable section
open Matrix
namespace FreeEntropy.LieMatrixCasimir
set_option backward.isDefEq.respectTransparency false
variable {d : ℕ} {H K B : Type*} [Fintype H] [DecidableEq H]
  [Fintype K] [DecidableEq K] [Fintype B] [DecidableEq B]

theorem Generators.dual_dual_E (R : Generators d H) (i j : Fin d) :
    R.dual.dual.E i j = R.E i j := by simp [Generators.dual]

theorem Generators.dual_tensor_E (R : Generators d H) (S : Generators d K) (i j : Fin d) :
    (R.tensor S).dual.E i j = (R.dual.tensor S.dual).E i j := by
  ext ⟨a,b⟩ ⟨c,e⟩
  by_cases h1 : a = c <;> by_cases h2 : b = e <;>
    simp [Generators.dual, Generators.tensor, Matrix.kronecker_apply, Matrix.one_apply,
      h1, h2, eq_comm, add_comm]

theorem Generators.conjugate_eq_neg_dual (R : Generators d H) (i j : Fin d) :
    (R.E j i).map (starRingEnd ℂ) = -R.dual.E i j := by
  have h := congrArg Matrix.transpose (R.adjoint j i)
  simpa only [Matrix.conjTranspose_transpose, Generators.dual, neg_neg] using h

/-- Complex conjugating a star-compatible intertwiner gives its dual. -/
theorem conjugate_intertwines (R : Generators d H) (S : Generators d K)
    (W : Matrix K H ℂ) (hW : ∀ i j, S.E i j * W = W * R.E i j) (i j : Fin d) :
    S.dual.E i j * W.map (starRingEnd ℂ) = W.map (starRingEnd ℂ) * R.dual.E i j := by
  have h := congrArg (fun X => X.map (starRingEnd ℂ)) (hW j i)
  simp only [Matrix.map_mul, Generators.conjugate_eq_neg_dual, Matrix.neg_mul, Matrix.mul_neg] at h
  exact neg_injective h

/-- Reindex the two tensor factors, without conjugation. -/
def swapRows (W : Matrix (H × K) B ℂ) : Matrix (K × H) B ℂ := fun ka b => W ka.swap b

theorem swap_tensor_intertwines (R : Generators d H) (S : Generators d K)
    (N : Generators d B) (W : Matrix (H × K) B ℂ)
    (hW : ∀ i j, (R.tensor S).E i j * W = W * N.E i j) (i j : Fin d) :
    (S.tensor R).E i j * swapRows W = swapRows W * N.E i j := by
  ext ⟨b,a⟩ k
  have h := congrFun (congrFun (hW i j) (a,b)) k
  rw [CartanChoi.tensor_mul_entry] at h
  rw [CartanChoi.tensor_mul_entry]
  simpa only [swapRows, Matrix.mul_apply, add_comm] using h

end FreeEntropy.LieMatrixCasimir
