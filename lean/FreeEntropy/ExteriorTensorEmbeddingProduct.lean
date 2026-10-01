/-
Copyright (c) 2026 Free Entropy formalization contributors.
See LICENSE and NOTICE in the repository root for license and attribution.
-/

import FreeEntropy.ExteriorTensorEmbedding
import FreeEntropy.ExteriorTensorPermutation

/-! Every finite exterior tensor product is isometrically embedded in an
actual physical tensor power, with the exact matrix intertwining identity. -/
noncomputable section
open Matrix
open scoped BigOperators
namespace FreeEntropy.ExteriorRepresentation
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

section Rectangular
variable {I : Type*} [Fintype I] [DecidableEq I]
  {A B C : I → Type*} [∀ i, Fintype (A i)] [∀ i, Fintype (B i)] [∀ i, Fintype (C i)]
  [∀ i, DecidableEq (A i)] [∀ i, DecidableEq (B i)] [∀ i, DecidableEq (C i)]

def rectProduct (M : ∀ i, Matrix (A i) (B i) ℂ) : Matrix (∀ i, A i) (∀ i, B i) ℂ :=
  fun x y => ∏ i, M i (x i) (y i)

theorem rectProduct_mul (M : ∀ i, Matrix (A i) (B i) ℂ) (N : ∀ i, Matrix (B i) (C i) ℂ) :
    rectProduct (fun i => M i * N i) = rectProduct M * rectProduct N := by
  ext x y
  simp only [rectProduct, Matrix.mul_apply]
  rw [Fintype.prod_sum]
  simp only [Finset.prod_mul_distrib]

theorem rectProduct_adjoint (M : ∀ i, Matrix (A i) (B i) ℂ) :
    (rectProduct M)ᴴ = rectProduct (fun i => (M i)ᴴ) := by
  ext x y
  simp [rectProduct, Matrix.conjTranspose_apply]

theorem rectProduct_one : rectProduct (fun i => (1 : Matrix (A i) (A i) ℂ)) = 1 :=
  productMatrix_one

theorem rectProduct_isometry (M : ∀ i, Matrix (A i) (B i) ℂ)
    (hM : ∀ i, (M i)ᴴ * M i = 1) : (rectProduct M)ᴴ * rectProduct M = 1 := by
  rw [rectProduct_adjoint, ← rectProduct_mul]
  simp only [hM, rectProduct_one]

end Rectangular

variable {I : Type*} [Fintype I] [DecidableEq I] (height : I → ℕ) (d : ℕ)

abbrev FactorWords := (i : I) → Fin (height i) → Fin d

def factorEmbedding : Matrix (FactorWords height d) (TensorIndex (d := d) height) ℂ :=
  rectProduct (fun i => wedgeEmbedding d (height i))

theorem factorEmbedding_isometry : (factorEmbedding height d)ᴴ * factorEmbedding height d = 1 :=
  rectProduct_isometry _ (fun i => wedgeEmbedding_isometry)

theorem factorEmbedding_intertwines (U : Matrix (Fin d) (Fin d) ℂ) :
    rectProduct (fun i => TensorPowers.matrix (height i) U) * factorEmbedding height d =
      factorEmbedding height d * tensorMatrix height U := by
  change rectProduct (fun i => TensorPowers.matrix (height i) U) *
      rectProduct (fun i => wedgeEmbedding d (height i)) =
    rectProduct (fun i => wedgeEmbedding d (height i)) * rectProduct (fun i => exteriorMatrix (height i) U)
  rw [← rectProduct_mul, ← rectProduct_mul]
  congr 1
  funext i
  exact wedgeEmbedding_intertwines U

/-- All tensor positions, counted without assuming a diagram size formula. -/
def positionEquiv : (Σ i, Fin (height i)) ≃ Fin (∑ i, height i) :=
  (Fintype.equivFin _).trans (finCongr (by simp [Fintype.card_sigma]))

def factorWordEquiv : FactorWords height d ≃ (Fin (∑ i, height i) → Fin d) :=
  (Equiv.piCurry (fun i (_ : Fin (height i)) => Fin d)).symm.trans
    ((positionEquiv height).arrowCongr (Equiv.refl (Fin d)))

theorem factorWordEquiv_at (x : FactorWords height d) (i : I) (j : Fin (height i)) :
    factorWordEquiv height d x (positionEquiv height ⟨i, j⟩) = x i j := by
  simp [factorWordEquiv]
  rfl

def flattenPermutation : Matrix (Fin (∑ i, height i) → Fin d) (FactorWords height d) ℂ :=
  basisPermutation (factorWordEquiv height d)

theorem flattenPermutation_isometry :
    (flattenPermutation height d)ᴴ * flattenPermutation height d = 1 := basisPermutation_isometry _

theorem flattenedTensor_entry (U : Matrix (Fin d) (Fin d) ℂ) (x y : FactorWords height d) :
    TensorPowers.matrix (∑ i, height i) U (factorWordEquiv height d x) (factorWordEquiv height d y) =
      rectProduct (fun i => TensorPowers.matrix (height i) U) x y := by
  change (∏ p, U (factorWordEquiv height d x p) (factorWordEquiv height d y p)) = _
  rw [← (positionEquiv height).prod_comp]
  simp only [Fintype.prod_sigma, factorWordEquiv_at, rectProduct, TensorPowers.matrix]

theorem flattenPermutation_intertwines (U : Matrix (Fin d) (Fin d) ℂ) :
    TensorPowers.matrix (∑ i, height i) U * flattenPermutation height d =
      flattenPermutation height d * rectProduct (fun i => TensorPowers.matrix (height i) U) :=
  basisPermutation_intertwines _ _ _ (flattenedTensor_entry height d U)

/-- The actual isometric exterior-tensor inclusion into ordinary physical words. -/
def exteriorTensorEmbedding : Matrix (Fin (∑ i, height i) → Fin d) (TensorIndex (d := d) height) ℂ :=
  flattenPermutation height d * factorEmbedding height d

theorem exteriorTensorEmbedding_isometry :
    (exteriorTensorEmbedding height d)ᴴ * exteriorTensorEmbedding height d = 1 := by
  simp only [exteriorTensorEmbedding, Matrix.conjTranspose_mul]
  calc
    _ = (factorEmbedding height d)ᴴ *
        ((flattenPermutation height d)ᴴ * flattenPermutation height d) * factorEmbedding height d := by
      simp only [Matrix.mul_assoc]
    _ = 1 := by rw [flattenPermutation_isometry, Matrix.mul_one, factorEmbedding_isometry]

theorem exteriorTensorEmbedding_intertwines (U : Matrix (Fin d) (Fin d) ℂ) :
    TensorPowers.matrix (∑ i, height i) U * exteriorTensorEmbedding height d =
      exteriorTensorEmbedding height d * tensorMatrix height U := by
  simp only [exteriorTensorEmbedding, ← Matrix.mul_assoc]
  rw [flattenPermutation_intertwines]
  rw [Matrix.mul_assoc, factorEmbedding_intertwines]
  simp only [Matrix.mul_assoc]

end FreeEntropy.ExteriorRepresentation
