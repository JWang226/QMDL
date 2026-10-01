/-
Copyright (c) 2026 Free Entropy formalization contributors.
See LICENSE and NOTICE in the repository root for license and attribution.
-/

import FreeEntropy.ExteriorTensorPermutation
import Mathlib.LinearAlgebra.Matrix.Kronecker

/-! Splitting exterior-tensor factors indexed by a disjoint sum gives the
literal Kronecker product, including the exact highest basis vector. -/
noncomputable section
open Matrix
open scoped BigOperators Kronecker
namespace FreeEntropy.ExteriorRepresentation
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false

variable {d : ℕ} {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    (height : I → ℕ) (height' : J → ℕ)

def tensorSumEquiv : TensorIndex (d := d) (Sum.elim height height') ≃
    TensorIndex (d := d) height × TensorIndex (d := d) height' :=
  Equiv.sumPiEquivProdPi (fun a => Index d (Sum.elim height height' a))

def tensorSumPermutation : Matrix
    (TensorIndex (d := d) height × TensorIndex (d := d) height')
    (TensorIndex (d := d) (Sum.elim height height')) ℂ :=
  basisPermutation (tensorSumEquiv height height')

theorem tensorSumPermutation_isometry :
    (tensorSumPermutation (d := d) height height')ᴴ * tensorSumPermutation (d := d) height height' = 1 :=
  basisPermutation_isometry _

theorem tensorSumPermutation_coisometry :
    tensorSumPermutation (d := d) height height' * (tensorSumPermutation (d := d) height height')ᴴ = 1 :=
  basisPermutation_coisometry _

theorem tensorSumMatrix_entry (U : Matrix (Fin d) (Fin d) ℂ)
    (x y : TensorIndex (d := d) (Sum.elim height height')) :
    (tensorMatrix height U ⊗ₖ tensorMatrix height' U)
      (tensorSumEquiv height height' x) (tensorSumEquiv height height' y) =
      tensorMatrix (Sum.elim height height') U x y := by
  simp only [tensorMatrix, productMatrix, tensorSumEquiv, Matrix.kronecker_apply,
    Fintype.prod_sum_type]
  rfl

theorem tensorSumPermutation_intertwines (U : Matrix (Fin d) (Fin d) ℂ) :
    (tensorMatrix height U ⊗ₖ tensorMatrix height' U) * tensorSumPermutation height height' =
      tensorSumPermutation height height' * tensorMatrix (Sum.elim height height') U :=
  basisPermutation_intertwines _ _ _ (tensorSumMatrix_entry height height' U)

theorem tensorSumEquiv_first (hh : ∀ i, height i ≤ d) (hh' : ∀ j, height' j ≤ d) :
    tensorSumEquiv height height'
      (tensorFirst (Sum.elim height height') (Sum.rec hh hh')) =
      (tensorFirst height hh, tensorFirst height' hh') := rfl

theorem tensorSumPermutation_highest (hh : ∀ i, height i ≤ d) (hh' : ∀ j, height' j ≤ d) :
    tensorSumPermutation height height' *ᵥ
      Pi.single (tensorFirst (Sum.elim height height') (Sum.rec hh hh')) 1 =
      Pi.single (tensorFirst height hh, tensorFirst height' hh') 1 := by
  change basisPermutation (tensorSumEquiv height height') *ᵥ _ = _
  rw [basisPermutation_single, tensorSumEquiv_first]

end FreeEntropy.ExteriorRepresentation
