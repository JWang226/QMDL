/-
Copyright (c) 2026 Free Entropy formalization contributors.
See LICENSE and NOTICE in the repository root for license and attribution.
-/

import FreeEntropy.ExteriorTensorPermutation
import FreeEntropy.TensorLieIntertwiners

/-! Literal flattening of two physical tensor powers, including the exact
sum-of-generators action obtained by differentiating the tensor identity. -/
noncomputable section
open Matrix
open scoped BigOperators Kronecker
namespace FreeEntropy.TensorPowers
open ExteriorRepresentation
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
variable {d n m : ℕ}

def wordPairEquiv : ((Fin n → Fin d) × (Fin m → Fin d)) ≃ (Fin (n + m) → Fin d) :=
  (Equiv.sumArrowEquivProdArrow (Fin n) (Fin m) (Fin d)).symm.trans
    (finSumFinEquiv.arrowCongr (Equiv.refl (Fin d)))

def pairFlatten : Matrix (Fin (n + m) → Fin d) ((Fin n → Fin d) × (Fin m → Fin d)) ℂ :=
  basisPermutation wordPairEquiv

theorem pairFlatten_isometry : (pairFlatten (d := d) (n := n) (m := m))ᴴ *
    pairFlatten (d := d) (n := n) (m := m) = 1 :=
  basisPermutation_isometry _

theorem pairFlatten_entry (U : Matrix (Fin d) (Fin d) ℂ)
    (x y : (Fin n → Fin d) × (Fin m → Fin d)) :
    matrix (n + m) U (wordPairEquiv x) (wordPairEquiv y) =
      matrix n U x.1 y.1 * matrix m U x.2 y.2 := by
  change (∏ t, U (wordPairEquiv x t) (wordPairEquiv y t)) = _
  rw [← (finSumFinEquiv : Fin n ⊕ Fin m ≃ Fin (n + m)).prod_comp]
  simp only [wordPairEquiv, Equiv.trans_apply, Equiv.arrowCongr_apply,
    Function.comp_apply, Equiv.symm_apply_apply, Equiv.refl_apply, Fintype.prod_sum_type]
  rfl

theorem pairFlatten_intertwines (U : Matrix (Fin d) (Fin d) ℂ) :
    matrix (n + m) U * pairFlatten = pairFlatten * (matrix n U ⊗ₖ matrix m U) :=
  basisPermutation_intertwines wordPairEquiv _ _ (pairFlatten_entry U)

theorem pairFlatten_differential_entry (A : Matrix (Fin d) (Fin d) ℂ)
    (x y : (Fin n → Fin d) × (Fin m → Fin d)) :
    differential (n + m) A (wordPairEquiv x) (wordPairEquiv y) =
      (differential n A ⊗ₖ (1 : Matrix (Fin m → Fin d) (Fin m → Fin d) ℂ) +
        (1 : Matrix (Fin n → Fin d) (Fin n → Fin d) ℂ) ⊗ₖ differential m A) x y := by
  have hL := hasDerivAt_matrix_identity (n + m) A (wordPairEquiv x) (wordPairEquiv y)
  simp only [pairFlatten_entry] at hL
  have hR := (hasDerivAt_matrix_identity n A x.1 y.1).mul
    (hasDerivAt_matrix_identity m A x.2 y.2)
  simp only [zero_smul, add_zero, matrix_one] at hR
  exact hL.unique hR

theorem pairFlatten_differential (A : Matrix (Fin d) (Fin d) ℂ) :
    differential (n + m) A * pairFlatten = pairFlatten *
      (differential n A ⊗ₖ (1 : Matrix (Fin m → Fin d) (Fin m → Fin d) ℂ) +
        (1 : Matrix (Fin n → Fin d) (Fin n → Fin d) ℂ) ⊗ₖ differential m A) :=
  basisPermutation_intertwines wordPairEquiv _ _ (pairFlatten_differential_entry A)

variable {A B : Type*} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]

def pairEmbedding (J : Matrix (Fin n → Fin d) A ℂ) (K : Matrix (Fin m → Fin d) B ℂ) :
    Matrix (Fin (n + m) → Fin d) (A × B) ℂ := pairFlatten * (J ⊗ₖ K)

theorem pairEmbedding_isometry (J : Matrix (Fin n → Fin d) A ℂ)
    (K : Matrix (Fin m → Fin d) B ℂ) (hJ : Jᴴ * J = 1) (hK : Kᴴ * K = 1) :
    (pairEmbedding J K)ᴴ * pairEmbedding J K = 1 := by
  let P := pairFlatten (d := d) (n := n) (m := m)
  have hP : Pᴴ * P = 1 := pairFlatten_isometry
  change (P * (J ⊗ₖ K))ᴴ * (P * (J ⊗ₖ K)) = 1
  rw [Matrix.conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc Pᴴ P, hP, Matrix.one_mul]
  rw [Matrix.conjTranspose_kronecker, ← Matrix.mul_kronecker_mul, hJ, hK, Matrix.one_kronecker_one]

theorem pairEmbedding_intertwines (J : Matrix (Fin n → Fin d) A ℂ)
    (K : Matrix (Fin m → Fin d) B ℂ) (U : Matrix (Fin d) (Fin d) ℂ)
    (R : Matrix A A ℂ) (S : Matrix B B ℂ)
    (hJ : matrix n U * J = J * R) (hK : matrix m U * K = K * S) :
    matrix (n + m) U * pairEmbedding J K = pairEmbedding J K * (R ⊗ₖ S) := by
  rw [pairEmbedding, ← Matrix.mul_assoc, pairFlatten_intertwines, Matrix.mul_assoc,
    ← Matrix.mul_kronecker_mul, hJ, hK, Matrix.mul_kronecker_mul, ← Matrix.mul_assoc]

theorem pairEmbedding_generators (J : Matrix (Fin n → Fin d) A ℂ)
    (K : Matrix (Fin m → Fin d) B ℂ)
    (E : LieMatrixCasimir.Generators d A) (F : LieMatrixCasimir.Generators d B)
    (hE : ∀ i j, (generators d n).E i j * J = J * E.E i j)
    (hF : ∀ i j, (generators d m).E i j * K = K * F.E i j) (i j : Fin d) :
    (generators d (n + m)).E i j * pairEmbedding J K =
      pairEmbedding J K * (E.tensor F).E i j := by
  change differential (n + m) (Matrix.single i j 1) * (pairFlatten * (J ⊗ₖ K)) = _
  rw [← Matrix.mul_assoc, pairFlatten_differential, Matrix.mul_assoc, Matrix.add_mul,
    ← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul]
  change pairFlatten * (((generators d n).E i j * J) ⊗ₖ (1 * K) +
    (1 * J) ⊗ₖ ((generators d m).E i j * K)) = _
  rw [hE, hF]
  simp only [Matrix.one_mul, LieMatrixCasimir.Generators.tensor, pairEmbedding,
    Matrix.mul_assoc, Matrix.mul_add, ← Matrix.mul_kronecker_mul, Matrix.mul_one]

end FreeEntropy.TensorPowers
