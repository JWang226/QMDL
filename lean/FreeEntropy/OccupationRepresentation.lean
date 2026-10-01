/-
Copyright (c) 2026 Free Entropy formalization contributors.
See LICENSE and NOTICE in the repository root for license and attribution.
-/

import FreeEntropy.Occupation
import FreeEntropy.WordPermutations

/-!
# The genuine symmetric-power matrix representation

The occupation subspace is characterized by constant amplitudes on word
contents. Tensor powers preserve it, so compression gives an actual monoid
representation, and a unitary representation for unitary inputs.
-/
noncomputable section
open scoped BigOperators Matrix.Norms.Elementwise
open Matrix
namespace FreeEntropy.Occupation
open WordTypes
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
variable {d n : ℕ}

def sampleWord (a : Occupation d n) : Words (n := n) a.val := Classical.choice (words_nonempty a)

def contentCoordinates (v : (Fin n → Fin d) → ℂ) (a : Occupation d n) : ℂ :=
  (Real.sqrt (typeSize a) : ℂ) * v (sampleWord a).val

theorem basis_mulVec_contentCoordinates {v : (Fin n → Fin d) → ℂ}
    (hv : ContentInvariant v) : basis *ᵥ contentCoordinates v = v := by
  funext w
  rw [Matrix.mulVec, dotProduct, Finset.sum_eq_single (ofWord w)]
  · have hs : (Real.sqrt (typeSize (ofWord w)) : ℂ) ≠ 0 := by
      exact_mod_cast (Real.sqrt_pos.mpr (by exact_mod_cast typeSize_pos (ofWord w))).ne'
    rw [basis, if_pos (show content w = (ofWord w).val from rfl), contentCoordinates,
      inv_mul_cancel_left₀ hs]
    exact hv _ _ (sampleWord (ofWord w)).property
  · intro a _ ha
    have hne : content w ≠ a.val := fun h => ha (Subtype.ext h.symm)
    simp [basis, hne]
  · simp

theorem basis_column_contentInvariant (a : Occupation d n) :
    ContentInvariant (fun w => basis w a) := by
  intro x y hxy
  simp only [basis, hxy]

/-- Every content-invariant vector is in the actual occupation range. -/
theorem projection_fixes_contentInvariant {v : (Fin n → Fin d) → ℂ}
    (hv : ContentInvariant v) : (basis * basisᴴ) *ᵥ v = v := by
  calc
    _ = (basis * basisᴴ) *ᵥ (basis *ᵥ contentCoordinates v) := by
      rw [basis_mulVec_contentCoordinates hv]
    _ = basis *ᵥ contentCoordinates v := by
      rw [Matrix.mulVec_mulVec, Matrix.mul_assoc, basis_isometry, Matrix.mul_one]
    _ = v := basis_mulVec_contentCoordinates hv

/-- Tensor powers preserve the range of the occupation isometry. -/
theorem tensor_preserves_range (A : Matrix (Fin d) (Fin d) ℂ) :
    (basis (d := d) (n := n) * (basis (d := d) (n := n))ᴴ) *
      (TensorPowers.matrix n A * basis (d := d) (n := n)) =
      TensorPowers.matrix n A * basis (d := d) (n := n) := by
  ext w a
  have h := projection_fixes_contentInvariant ((basis_column_contentInvariant a).tensor_action A)
  simpa only [Matrix.mul_apply, Matrix.mulVec, dotProduct] using congrFun h w

/-- Symmetric-power action constructed by compressing the real tensor action. -/
def symmetricMatrix (A : Matrix (Fin d) (Fin d) ℂ) :
    Matrix (Occupation d n) (Occupation d n) ℂ := basisᴴ * TensorPowers.matrix n A * basis

theorem symmetricMatrix_intertwines (A : Matrix (Fin d) (Fin d) ℂ) :
    TensorPowers.matrix n A * basis = basis * symmetricMatrix (n := n) A := by
  rw [symmetricMatrix]
  simpa only [Matrix.mul_assoc] using (tensor_preserves_range (n := n) A).symm

theorem symmetricMatrix_one : symmetricMatrix (d := d) (n := n) 1 = 1 := by
  rw [symmetricMatrix, TensorPowers.matrix_one, Matrix.mul_one, basis_isometry]

theorem symmetricMatrix_mul (A B : Matrix (Fin d) (Fin d) ℂ) :
    symmetricMatrix (n := n) (A * B) = symmetricMatrix (n := n) A * symmetricMatrix (n := n) B := by
  let V := basis (d := d) (n := n)
  change Vᴴ * TensorPowers.matrix n (A * B) * V =
    (Vᴴ * TensorPowers.matrix n A * V) * (Vᴴ * TensorPowers.matrix n B * V)
  rw [TensorPowers.matrix_mul]
  have h : (V * Vᴴ) * (TensorPowers.matrix n B * V) = TensorPowers.matrix n B * V :=
    tensor_preserves_range (n := n) B
  calc
    _ = Vᴴ * TensorPowers.matrix n A * (TensorPowers.matrix n B * V) := by
      simp only [Matrix.mul_assoc]
    _ = Vᴴ * TensorPowers.matrix n A * ((V * Vᴴ) * (TensorPowers.matrix n B * V)) := by
      rw [h]
    _ = _ := by simp only [Matrix.mul_assoc]

theorem symmetricMatrix_adjoint (A : Matrix (Fin d) (Fin d) ℂ) :
    symmetricMatrix (n := n) Aᴴ = (symmetricMatrix (n := n) A)ᴴ := by
  simp [symmetricMatrix, TensorPowers.matrix_adjoint, Matrix.mul_assoc]

theorem symmetricMatrix_unitary {U : Matrix (Fin d) (Fin d) ℂ} (hU : Uᴴ * U = 1) :
    (symmetricMatrix (n := n) U)ᴴ * symmetricMatrix (n := n) U = 1 := by
  rw [← symmetricMatrix_adjoint, ← symmetricMatrix_mul, hU, symmetricMatrix_one]

/-- An actual group/monoid action on the occupation basis. -/
def symmetricRepresentation {G : Type*} [Monoid G] (U : G →* Matrix (Fin d) (Fin d) ℂ) :
    G →* Matrix (Occupation d n) (Occupation d n) ℂ where
  toFun g := symmetricMatrix (n := n) (U g)
  map_one' := by rw [map_one, symmetricMatrix_one]
  map_mul' g h := by rw [map_mul, symmetricMatrix_mul]

/-- Equivariance of the actual pure-state occupation coefficients. -/
theorem coefficients_action (U : Matrix (Fin d) (Fin d) ℂ) (v : Fin d → ℂ) :
    symmetricMatrix (n := n) U *ᵥ coefficients v = coefficients (U *ᵥ v) := by
  have hinj : Function.Injective (fun v : Occupation d n → ℂ => basis *ᵥ v) := by
    intro v w h
    have hh := congrArg (fun x => basisᴴ *ᵥ x) h
    simpa only [Matrix.mulVec_mulVec, basis_isometry, Matrix.one_mulVec] using hh
  apply hinj
  change basis *ᵥ (symmetricMatrix (n := n) U *ᵥ coefficients v) = basis *ᵥ coefficients (U *ᵥ v)
  rw [Matrix.mulVec_mulVec, ← symmetricMatrix_intertwines, ← Matrix.mulVec_mulVec,
    basis_mulVec_coefficients, basis_mulVec_coefficients]
  exact TensorPowers.vector_action n U v

/-- Continuity of the actual finite tensor-polynomial matrix entries. -/
theorem tensor_matrix_continuous :
    Continuous (TensorPowers.matrix n : Matrix (Fin d) (Fin d) ℂ →
      Matrix (Fin n → Fin d) (Fin n → Fin d) ℂ) := by
  apply continuous_matrix
  intro x y
  exact continuous_finset_prod _ (fun t _ => (continuous_apply (y t)).comp (continuous_apply (x t)))

/-- The symmetric-power action is continuous in the physical matrix. -/
theorem symmetricMatrix_continuous : Continuous (symmetricMatrix (d := d) (n := n)) :=
  (continuous_const.matrix_mul tensor_matrix_continuous).matrix_mul continuous_const

end FreeEntropy.Occupation
