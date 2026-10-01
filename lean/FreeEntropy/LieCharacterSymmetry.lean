/-
Copyright (c) 2026 Free Entropy formalization contributors.
See LICENSE and NOTICE in the repository root for license and attribution.
-/

import FreeEntropy.LieCharacterRadial
import FreeEntropy.ExteriorWeightCoordinates
import FreeEntropy.ExteriorPhysicalIrrep
import FreeEntropy.TensorWeightSource
import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.LinearAlgebra.Matrix.Permutation

/-! Character symmetry is proved from the actual physical tensor embedding
and physical permutation unitaries, not supplied as a Weyl-theory premise. -/
noncomputable section
open Matrix
open scoped BigOperators
namespace FreeEntropy.LieCharacter
open SchurWeyl
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option linter.unusedSectionVars false
variable {d n : ℕ} {H : Type*} [Fintype H] [DecidableEq H]

theorem eval_weightMonomial (w : Fin d → ℕ) (z : Fin d → ℂ) :
    MvPolynomial.eval z (weightMonomial w) = ∏ j, z j ^ w j := by
  rw [weightMonomial, MvPolynomial.eval_monomial, one_mul]
  exact Finsupp.prod_fintype _ _ (fun _ => pow_zero _)

theorem eval_character (weight : H → Fin d → ℕ) (z : Fin d → ℂ) :
    MvPolynomial.eval z (character weight) = ∑ a, ∏ j, z j ^ weight a j := by
  simp only [character, map_sum, eval_weightMonomial]

/-- The literal tensor diagonal action on columns of a natural weight basis. -/
theorem physical_weight_source (J : Matrix (Fin n → Fin d) H ℂ)
    (weight : H → Fin d → ℕ)
    (hE : ∀ j, (TensorPowers.generators d n).E j j * J =
      J * Matrix.diagonal (fun a => (weight a j : ℂ))) (z : Fin d → ℂ) :
    TensorPowers.matrix n (Matrix.diagonal z) * J =
      J * Matrix.diagonal (fun a => ∏ j, z j ^ weight a j) := by
  rw [Occupation.tensor_diagonal]
  ext w a
  rw [Matrix.diagonal_mul, Matrix.mul_diagonal]
  by_cases hwa : J w a = 0
  · simp [hwa]
  · have hc : WordTypes.content w = weight a := by
      funext j
      have h := congrArg (fun M => M w a) (hE j)
      dsimp only at h
      rw [TensorPowers.generators_diagonal, Matrix.diagonal_mul, Matrix.mul_diagonal,
        mul_comm (J w a)] at h
      exact_mod_cast mul_right_cancel₀ hwa h
    rw [tensorVector_eq_character]
    change (∏ j, z j ^ WordTypes.content w j) * J w a = _
    rw [hc, mul_comm]

/-- Polynomial evaluation is the actual compressed physical source trace. -/
theorem eval_character_eq_trace (J : Matrix (Fin n → Fin d) H ℂ)
    (hJ : Jᴴ * J = 1) (weight : H → Fin d → ℕ)
    (hE : ∀ j, (TensorPowers.generators d n).E j j * J =
      J * Matrix.diagonal (fun a => (weight a j : ℂ))) (z : Fin d → ℂ) :
    MvPolynomial.eval z (character weight) =
      (Jᴴ * TensorPowers.matrix n (Matrix.diagonal z) * J).trace := by
  rw [Matrix.mul_assoc, physical_weight_source J weight hE,
    ← Matrix.mul_assoc, hJ, Matrix.one_mul, Matrix.trace_diagonal, eval_character]

def alphabetPermutation (e : Equiv.Perm (Fin d)) : Matrix.unitaryGroup (Fin d) ℂ :=
  ⟨e.permMatrix ℂ, Matrix.mem_unitaryGroup_iff'.mpr (by
    change (e.permMatrix ℂ)ᴴ * e.permMatrix ℂ = 1
    rw [Matrix.conjTranspose_permMatrix, ← Matrix.permMatrix_mul]
    simp)⟩

theorem alphabetPermutation_diagonal (e : Equiv.Perm (Fin d)) (z : Fin d → ℂ) :
    (alphabetPermutation e : Matrix (Fin d) (Fin d) ℂ) * Matrix.diagonal z *
      (alphabetPermutation e : Matrix (Fin d) (Fin d) ℂ)ᴴ = Matrix.diagonal (z ∘ e) := by
  change e.permMatrix ℂ * Matrix.diagonal z * (e.permMatrix ℂ)ᴴ = _
  rw [Matrix.conjTranspose_permMatrix]
  change e.toPEquiv.toMatrix * Matrix.diagonal z * e.symm.toPEquiv.toMatrix = _
  rw [PEquiv.toMatrix_toPEquiv_mul, PEquiv.mul_toMatrix_toPEquiv]
  ext i j
  simp [Matrix.submatrix_apply, Matrix.diagonal_apply]

/-- A reducing physical subspace has a conjugation-invariant source trace. -/
theorem compressed_trace_conjugate (J : Matrix (Fin n → Fin d) H ℂ)
    (hP : TensorCommutant (J * Jᴴ)) (U : Matrix.unitaryGroup (Fin d) ℂ)
    (A : Matrix (Fin d) (Fin d) ℂ) :
    (Jᴴ * TensorPowers.matrix n ((U : Matrix (Fin d) (Fin d) ℂ) * A *
      (U : Matrix (Fin d) (Fin d) ℂ)ᴴ) * J).trace =
      (Jᴴ * TensorPowers.matrix n A * J).trace := by
  let T := TensorPowers.matrix n (U : Matrix (Fin d) (Fin d) ℂ)
  have hT : Tᴴ * T = 1 := TensorPowers.matrix_unitary n (Matrix.UnitaryGroup.star_mul_self U)
  have hcomm : (J * Jᴴ) * T = T * (J * Jᴴ) := hP U
  rw [TensorPowers.matrix_covariance, Matrix.trace_mul_cycle]
  change (J * Jᴴ * (T * TensorPowers.matrix n A * Tᴴ)).trace = _
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hcomm, Matrix.mul_assoc,
    Matrix.trace_mul_cycle, Matrix.mul_assoc (TensorPowers.matrix n A) Tᴴ T, hT, Matrix.mul_one]
  rw [Matrix.trace_mul_cycle]
  exact Matrix.trace_mul_comm _ _

/-- Every actual physical natural-weight character is symmetric. -/
theorem character_rename_of_physical (J : Matrix (Fin n → Fin d) H ℂ)
    (hJ : Jᴴ * J = 1) (weight : H → Fin d → ℕ)
    (hE : ∀ j, (TensorPowers.generators d n).E j j * J =
      J * Matrix.diagonal (fun a => (weight a j : ℂ)))
    (hP : TensorCommutant (J * Jᴴ)) (e : Equiv.Perm (Fin d)) :
    MvPolynomial.rename e (character weight) = character weight := by
  apply MvPolynomial.funext
  intro z
  rw [MvPolynomial.eval_rename, eval_character_eq_trace J hJ weight hE,
    eval_character_eq_trace J hJ weight hE, ← alphabetPermutation_diagonal e z]
  exact compressed_trace_conjugate J hP (alphabetPermutation e) (Matrix.diagonal z)

end FreeEntropy.LieCharacter

namespace FreeEntropy.ExteriorRepresentation
open SchurWeyl LieCharacter
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
variable {d : ℕ}

/-- The actual canonical weight basis embedded in the literal word space. -/
def canonicalPhysicalWeightEmbedding (mu : Fin d → ℕ) :
    Matrix (Fin (tensorDegree mu) → Fin d) (IrrepIndex mu) ℂ :=
  irrepTensorEmbedding mu * (canonicalWeightCoordinates mu).unitary

theorem canonicalPhysicalWeightEmbedding_isometry (mu : Fin d → ℕ) :
    (canonicalPhysicalWeightEmbedding mu)ᴴ * canonicalPhysicalWeightEmbedding mu = 1 := by
  simp only [canonicalPhysicalWeightEmbedding, Matrix.conjTranspose_mul, Matrix.mul_assoc,
    ← Matrix.mul_assoc (irrepTensorEmbedding mu)ᴴ (irrepTensorEmbedding mu),
    irrepTensorEmbedding_isometry, Matrix.one_mul, (canonicalWeightCoordinates mu).isometry]

theorem canonicalPhysicalWeightEmbedding_generators (mu : Fin d → ℕ) (i j : Fin d) :
    (TensorPowers.generators d (tensorDegree mu)).E i j * canonicalPhysicalWeightEmbedding mu =
      canonicalPhysicalWeightEmbedding mu * (canonicalWeightModel mu).generators.E i j := by
  let W := (canonicalWeightCoordinates mu).unitary
  have hc : W * Wᴴ = 1 := mul_eq_one_comm.mp (canonicalWeightCoordinates mu).isometry
  change _ * (irrepTensorEmbedding mu * W) = _
  rw [← Matrix.mul_assoc, irrepGenerators_intertwines, Matrix.mul_assoc]
  rw [show (canonicalWeightModel mu).generators.E i j =
      Wᴴ * (irrepGenerators mu).E i j * W from (canonicalWeightCoordinates mu).generators i j]
  change irrepTensorEmbedding mu * ((irrepGenerators mu).E i j * W) =
    (irrepTensorEmbedding mu * W) * (Wᴴ * (irrepGenerators mu).E i j * W)
  simp only [Matrix.mul_assoc, ← Matrix.mul_assoc W Wᴴ, hc, Matrix.one_mul]

theorem canonicalPhysicalWeightEmbedding_diagonal (mu : Fin d → ℕ) (j : Fin d) :
    (TensorPowers.generators d (tensorDegree mu)).E j j * canonicalPhysicalWeightEmbedding mu =
      canonicalPhysicalWeightEmbedding mu * Matrix.diagonal (fun a => (canonicalWeight mu a j : ℂ)) := by
  rw [canonicalPhysicalWeightEmbedding_generators, (canonicalWeightModel mu).diagonal]
  congr 1
  ext a b
  simp only [WeightSectors.weightDiagonal, canonicalWeight_spec, Complex.ofReal_natCast]

theorem canonicalPhysicalWeightEmbedding_commutant (mu : Fin d → ℕ) :
    TensorCommutant (canonicalPhysicalWeightEmbedding mu * (canonicalPhysicalWeightEmbedding mu)ᴴ) := by
  have hp : canonicalPhysicalWeightEmbedding mu * (canonicalPhysicalWeightEmbedding mu)ᴴ =
      irrepTensorEmbedding mu * (irrepTensorEmbedding mu)ᴴ := by
    have hc := mul_eq_one_comm.mp (canonicalWeightCoordinates mu).isometry
    simp only [canonicalPhysicalWeightEmbedding, Matrix.conjTranspose_mul, Matrix.mul_assoc,
      ← Matrix.mul_assoc (canonicalWeightCoordinates mu).unitary
        (canonicalWeightCoordinates mu).unitaryᴴ, hc, Matrix.one_mul]
  rw [hp]
  exact copy_matrixUnit_commutant (irrepMatrix mu) (irrepTensorEmbedding mu)
    (irrepTensorEmbedding mu) (irrepTensorEmbedding_isometry mu)
    (irrepTensorEmbedding_intertwines mu) (irrepTensorEmbedding_intertwines mu)

/-- Symmetry of the literal canonical polynomial character, derived from its
constructed physical tensor embedding. No Weyl character formula is used. -/
theorem canonical_character_rename (mu : Fin d → ℕ) (e : Equiv.Perm (Fin d)) :
    MvPolynomial.rename e (LieCharacter.character (canonicalWeight mu)) =
      LieCharacter.character (canonicalWeight mu) :=
  LieCharacter.character_rename_of_physical (canonicalPhysicalWeightEmbedding mu)
    (canonicalPhysicalWeightEmbedding_isometry mu) (canonicalWeight mu)
    (canonicalPhysicalWeightEmbedding_diagonal mu)
    (canonicalPhysicalWeightEmbedding_commutant mu) e

end FreeEntropy.ExteriorRepresentation
