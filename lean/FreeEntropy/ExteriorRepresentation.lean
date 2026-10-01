/-
Copyright (c) 2026 Free Entropy formalization contributors.
See LICENSE and NOTICE in the repository root for license and attribution.
-/

import Mathlib.LinearAlgebra.ExteriorPower.Basis
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import FreeEntropy.UnitaryHaar

/-! Concrete exterior-power matrices in the actual subset-indexed wedge basis. -/
noncomputable section
open Matrix Module
open scoped BigOperators

namespace FreeEntropy.ExteriorRepresentation

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

abbrev Index (d k : ℕ) := Set.powersetCard (Fin d) k

instance (d k : ℕ) : DecidableEq (Index d k) := Classical.decEq _

def wedgeBasis (d k : ℕ) : Basis (Index d k) ℂ (⋀[ℂ]^k (Fin d → ℂ)) :=
  (Pi.basisFun ℂ (Fin d)).exteriorPower k

/-- The action is the genuine induced map on the exterior algebra. -/
def exteriorMatrix {d : ℕ} (k : ℕ) (A : Matrix (Fin d) (Fin d) ℂ) :
    Matrix (Index d k) (Index d k) ℂ :=
  LinearMap.toMatrix (wedgeBasis d k) (wedgeBasis d k)
    (exteriorPower.map k (Matrix.toLin' A))

theorem exteriorMatrix_one (d k : ℕ) : exteriorMatrix k (1 : Matrix (Fin d) (Fin d) ℂ) = 1 := by
  rw [exteriorMatrix, Matrix.toLin'_one, exteriorPower.map_id, LinearMap.toMatrix_id]

theorem exteriorMatrix_mul {d : ℕ} (k : ℕ) (A B : Matrix (Fin d) (Fin d) ℂ) :
    exteriorMatrix k (A * B) = exteriorMatrix k A * exteriorMatrix k B := by
  rw [exteriorMatrix, Matrix.toLin'_mul, exteriorPower.map_comp,
    LinearMap.toMatrix_comp (wedgeBasis d k) (wedgeBasis d k) (wedgeBasis d k)]
  rfl

/-- Increasing enumeration of a literal k-element subset. -/
def enumerate {d k : ℕ} (s : Index d k) : Fin k ↪o Fin d :=
  Set.powersetCard.ofFinEmbEquiv.symm s

/-- Matrix coefficients are the actual k-by-k minors. -/
theorem exteriorMatrix_apply {d k : ℕ} (A : Matrix (Fin d) (Fin d) ℂ)
    (s t : Index d k) :
    exteriorMatrix k A s t = (A.submatrix (enumerate s) (enumerate t)).det := by
  rw [exteriorMatrix, LinearMap.toMatrix_apply]
  simp only [wedgeBasis, exteriorPower.basis_apply, exteriorPower.ιMulti_family,
    exteriorPower.map_apply_ιMulti, exteriorPower.basis_repr_apply,
    exteriorPower.ιMultiDual_apply_ιMulti]
  rw [← Matrix.det_transpose]
  congr 1
  ext i j
  simp [enumerate, Matrix.toLin'_apply, Pi.basisFun_apply,
    Matrix.submatrix_apply]

theorem exteriorMatrix_adjoint {d k : ℕ} (A : Matrix (Fin d) (Fin d) ℂ) :
    exteriorMatrix k Aᴴ = (exteriorMatrix k A)ᴴ := by
  ext s t
  rw [exteriorMatrix_apply, Matrix.conjTranspose_apply, exteriorMatrix_apply]
  have hm : Aᴴ.submatrix (enumerate s) (enumerate t) =
      (A.submatrix (enumerate t) (enumerate s))ᴴ := rfl
  rw [hm, Matrix.det_conjTranspose]

theorem exteriorMatrix_unitary {d k : ℕ} {U : Matrix (Fin d) (Fin d) ℂ}
    (hU : Uᴴ * U = 1) : (exteriorMatrix k U)ᴴ * exteriorMatrix k U = 1 := by
  rw [← exteriorMatrix_adjoint, ← exteriorMatrix_mul, hU, exteriorMatrix_one]

def unitaryRepresentation (d k : ℕ) : Matrix.unitaryGroup (Fin d) ℂ →*
    Matrix (Index d k) (Index d k) ℂ where
  toFun U := exteriorMatrix k U.val
  map_one' := exteriorMatrix_one d k
  map_mul' U V := exteriorMatrix_mul k U.val V.val

theorem unitaryRepresentation_unitary (d k : ℕ) (U : Matrix.unitaryGroup (Fin d) ℂ) :
    (unitaryRepresentation d k U)ᴴ * unitaryRepresentation d k U = 1 :=
  exteriorMatrix_unitary (Matrix.UnitaryGroup.star_mul_self U)

/-- Character of the k-subset: the product of its selected diagonal entries. -/
def character {d k : ℕ} (z : Fin d → ℂ) (s : Index d k) : ℂ :=
  ∏ i : Fin k, z (enumerate s i)

theorem exterior_diagonal_basis {d k : ℕ} (z : Fin d → ℂ) (s : Index d k) :
    exteriorPower.map k (Matrix.toLin' (diagonal z)) (wedgeBasis d k s) =
      character z s • wedgeBasis d k s := by
  simp only [wedgeBasis, exteriorPower.basis_apply, exteriorPower.ιMulti_family,
    exteriorPower.map_apply_ιMulti]
  have hv : Matrix.toLin' (diagonal z) ∘ (Pi.basisFun ℂ (Fin d) ∘ enumerate s) =
      fun i => z (enumerate s i) • Pi.basisFun ℂ (Fin d) (enumerate s i) := by
    funext i j
    simp [Matrix.toLin'_apply, Matrix.mulVec_diagonal, Pi.basisFun_apply,
      Pi.single_apply, smul_eq_mul]
    split_ifs with h
    · rw [h]
    · simp
  change exteriorPower.ιMulti ℂ k
    (Matrix.toLin' (diagonal z) ∘ (Pi.basisFun ℂ (Fin d) ∘ enumerate s)) = _
  rw [hv]
  exact (exteriorPower.ιMulti ℂ k).toMultilinearMap.map_smul_univ _ _

theorem exteriorMatrix_diagonal {d k : ℕ} (z : Fin d → ℂ) :
    exteriorMatrix k (diagonal z) = diagonal (character (k := k) z) := by
  ext s t
  rw [exteriorMatrix, LinearMap.toMatrix_apply, exterior_diagonal_basis]
  simp only [map_smul, Basis.repr_self, Finsupp.smul_apply, Finsupp.single_apply,
    smul_eq_mul, Matrix.diagonal_apply]
  by_cases h : t = s
  · subst t; simp
  · simp [h, Ne.symm h]

theorem exteriorMatrix_continuous (d k : ℕ) :
    Continuous (exteriorMatrix (d := d) k) := by
  apply continuous_pi
  intro s
  apply continuous_pi
  intro t
  simp_rw [exteriorMatrix_apply]
  fun_prop

theorem unitaryRepresentation_continuous (d k : ℕ) :
    Continuous (unitaryRepresentation d k) :=
  (exteriorMatrix_continuous d k).comp continuous_subtype_val

end FreeEntropy.ExteriorRepresentation
