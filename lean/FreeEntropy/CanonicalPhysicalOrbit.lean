/-
Copyright (c) 2026 Free Entropy formalization contributors.
See LICENSE and NOTICE in the repository root for license and attribution.
-/

import FreeEntropy.PhysicalCanonicalChannels
import FreeEntropy.CanonicalOrbit

/-! The canonical compressed physical tensor state has the actual canonical
unitary covariance, both in original and natural weight coordinates. -/
noncomputable section
open Matrix
open scoped BigOperators MatrixOrder ComplexOrder
namespace FreeEntropy.SchurWeyl
open ExteriorRepresentation
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
variable {d r n : ℕ}

theorem canonicalTensorSource_covariance (mu : Fin d → ℕ)
    (U : Matrix.unitaryGroup (Fin d) ℂ) (ρ : Matrix (Fin d) (Fin d) ℂ) :
    canonicalTensorSource mu ((U : Matrix (Fin d) (Fin d) ℂ) * ρ *
      (U : Matrix (Fin d) (Fin d) ℂ)ᴴ) =
      irrepMatrix mu U * canonicalTensorSource mu ρ * (irrepMatrix mu U)ᴴ := by
  let J := irrepTensorEmbedding mu
  let R := irrepMatrix mu
  let t := tensorDegree mu
  have hL := intertwiner_adjoint R J (irrepTensorEmbedding_isometry mu)
    (irrepTensorEmbedding_intertwines mu) U
  have hR := irrepTensorEmbedding_intertwines mu U⁻¹
  change physicalRepresentation d t U⁻¹ * J = J * R U⁻¹ at hR
  rw [Twirling.inverse_eq_conjTranspose (physicalRepresentation d t)
    (physicalRepresentation_unitary d t),
    Twirling.inverse_eq_conjTranspose R (irrepMatrix_unitary mu)] at hR
  unfold canonicalTensorSource
  rw [TensorPowers.matrix_covariance]
  change Jᴴ * (physicalRepresentation d t U * TensorPowers.matrix t ρ *
    (physicalRepresentation d t U)ᴴ) * J = R U * (Jᴴ * TensorPowers.matrix t ρ * J) * (R U)ᴴ
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc Jᴴ (physicalRepresentation d t U), hL]
  simp only [Matrix.mul_assoc]
  rw [show (physicalRepresentation d t U)ᴴ * J = J * (R U)ᴴ from hR]

theorem canonicalTensorState_covariance (mu : Fin d → ℕ)
    (U : Matrix.unitaryGroup (Fin d) ℂ) (ρ : Matrix (Fin d) (Fin d) ℂ) :
    canonicalTensorState mu ((U : Matrix (Fin d) (Fin d) ℂ) * ρ *
      (U : Matrix (Fin d) (Fin d) ℂ)ᴴ) =
      irrepMatrix mu U * canonicalTensorState mu ρ * (irrepMatrix mu U)ᴴ := by
  letI : Nonempty (IrrepIndex mu) := Fin.pos_iff_nonempty.mp (irrep_dimension_pos mu)
  unfold canonicalTensorState
  rw [canonicalTensorSource_covariance, normalizedBlock_unitary _ (irrepMatrix_unitary mu U)
    (mul_eq_one_comm.mp (irrepMatrix_unitary mu U))]

def canonicalWeightTensorState (mu : Fin d → ℕ) (ρ : Matrix (Fin d) (Fin d) ℂ) :
    Matrix (IrrepIndex mu) (IrrepIndex mu) ℂ :=
  (canonicalWeightCoordinates mu).unitaryᴴ * canonicalTensorState mu ρ *
    (canonicalWeightCoordinates mu).unitary

/-- Physical tensor covariance in the parent's actual canonical weight representation. -/
theorem canonicalWeightTensorState_diagonal_orbit (mu : Fin d → ℕ)
    (U : Matrix.unitaryGroup (Fin d) ℂ) (z : Fin d → ℂ) :
    canonicalWeightTensorState mu ((U : Matrix (Fin d) (Fin d) ℂ) * Matrix.diagonal z *
      (U : Matrix (Fin d) (Fin d) ℂ)ᴴ) =
      canonicalWeightRepresentation mu U * canonicalMonomialState mu z *
        (canonicalWeightRepresentation mu U)ᴴ := by
  rw [canonicalWeightTensorState, canonicalTensorState_covariance,
    ← canonicalTensorState_weight_diagonal]
  let Q := (canonicalWeightCoordinates mu).unitary
  have hQ : Q * Qᴴ = 1 := mul_eq_one_comm.mp (canonicalWeightCoordinates mu).isometry
  change Qᴴ * (irrepMatrix mu U * canonicalTensorState mu (Matrix.diagonal z) *
    (irrepMatrix mu U)ᴴ) * Q =
      (Qᴴ * irrepMatrix mu U * Q) * (Qᴴ * canonicalTensorState mu (Matrix.diagonal z) * Q) *
        (Qᴴ * irrepMatrix mu U * Q)ᴴ
  simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
    Matrix.mul_assoc, ← Matrix.mul_assoc Q Qᴴ, hQ, Matrix.one_mul]

/-- Actual classification unitary directly into the natural weight coordinates. -/
def sectorWeightCanonicalUnitary (i : Sector d n) :
    Matrix (IrrepIndex (sectorHighestOccupation i).val) (SectorSpace d n i) ℂ :=
  (canonicalWeightCoordinates (sectorHighestOccupation i).val).unitaryᴴ * sectorCanonicalUnitary i

theorem sectorWeightCanonicalUnitary_isometry (i : Sector d n) :
    (sectorWeightCanonicalUnitary i)ᴴ * sectorWeightCanonicalUnitary i = 1 := by
  let Q := (canonicalWeightCoordinates (sectorHighestOccupation i).val).unitary
  have hQ : Q * Qᴴ = 1 := mul_eq_one_comm.mp (canonicalWeightCoordinates _).isometry
  change (Qᴴ * sectorCanonicalUnitary i)ᴴ * (Qᴴ * sectorCanonicalUnitary i) = 1
  simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc,
    ← Matrix.mul_assoc Q Qᴴ, hQ, Matrix.one_mul, (sectorCanonicalUnitary_spec i).1]

theorem sectorWeightCanonicalUnitary_coisometry (i : Sector d n) :
    sectorWeightCanonicalUnitary i * (sectorWeightCanonicalUnitary i)ᴴ = 1 := by
  simp only [sectorWeightCanonicalUnitary, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc,
    ← Matrix.mul_assoc (sectorCanonicalUnitary i) (sectorCanonicalUnitary i)ᴴ,
    (sectorCanonicalUnitary_spec i).2.1, Matrix.one_mul, (canonicalWeightCoordinates _).isometry]

/-- Source identification directly in canonical natural weight coordinates. -/
theorem sectorState_canonicalWeight (i : Sector d n) {ρ : Matrix (Fin d) (Fin d) ℂ}
    (hρ : ρ.IsHermitian) :
    sectorWeightCanonicalUnitary i * sectorState n ρ i * (sectorWeightCanonicalUnitary i)ᴴ =
      canonicalWeightTensorState (sectorHighestOccupation i).val ρ := by
  have h := congrArg (fun X => (canonicalWeightCoordinates (sectorHighestOccupation i).val).unitaryᴴ *
    X * (canonicalWeightCoordinates (sectorHighestOccupation i).val).unitary) (sectorState_canonical i hρ)
  simpa only [sectorWeightCanonicalUnitary, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_conjTranspose, canonicalWeightTensorState, Matrix.mul_assoc] using h

end FreeEntropy.SchurWeyl
