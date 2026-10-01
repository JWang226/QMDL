/-
Copyright (c) 2026 Free Entropy formalization contributors.
See LICENSE and NOTICE in the repository root for license and attribution.
-/

import FreeEntropy.ExteriorDominant
import FreeEntropy.TorusWeightEigenline

/-! A genuinely constructed irreducible U(d) representation at each
dominant natural highest weight, as an actual cyclic exterior tensor subspace. -/

noncomputable section
open Matrix
open scoped BigOperators
namespace FreeEntropy.ExteriorRepresentation
open UnitaryDecomposition

set_option backward.isDefEq.respectTransparency false

variable {d : ℕ} (mu : Fin d → ℕ)

abbrev AmbientIndex := TensorIndex (d := d) (columnHeight mu)

def ambientRepresentation : Matrix.unitaryGroup (Fin d) ℂ →*
    Matrix (AmbientIndex mu) (AmbientIndex mu) ℂ :=
  tensorRepresentation (columnHeight mu)

def highestBasisIndex : AmbientIndex mu := tensorFirst (columnHeight mu) (columnHeight_le mu)

def highestVector : EuclideanSpace ℂ (AmbientIndex mu) :=
  TorusWeights.highestVector (highestBasisIndex mu)

def highestSubspace : Submodule ℂ (EuclideanSpace ℂ (AmbientIndex mu)) :=
  cyclicSubspace (euclideanRepresentation (ambientRepresentation mu)) (highestVector mu)

theorem highestSubspace_irreducible :
    IrreducibleSubspace (euclideanRepresentation (ambientRepresentation mu))
      (highestSubspace mu) := by
  apply TorusWeights.cyclic_irreducible (ambientRepresentation mu)
    (tensorRepresentation_unitary (columnHeight mu)) Occupation.diagonalUnitary
    (tensorWeight (columnHeight mu))
  · intro z hz
    exact tensorMatrix_diagonal (columnHeight mu) z
  · intro x hx
    exact (tensorWeight_eq_highest_iff (columnHeight mu) (columnHeight_le mu) x).mp hx

theorem highestVector_weight (hmu : Antitone mu) (z : Fin d → ℂ) (hz : ∀ i, ‖z i‖ = 1) :
    euclideanRepresentation (ambientRepresentation mu) (Occupation.diagonalUnitary z hz)
      (highestVector mu) = (∏ i, z i ^ mu i) • highestVector mu := by
  apply PiLp.ext
  intro x
  change (tensorMatrix (columnHeight mu) (diagonal z) *ᵥ
    (Pi.single (highestBasisIndex mu) 1 : AmbientIndex mu → ℂ)) x = _
  rw [tensorMatrix_diagonal, Matrix.mulVec_diagonal]
  by_cases hx : x = highestBasisIndex mu
  · subst x
    simp [highestVector, TorusWeights.highestVector, highestBasisIndex, tensorFirst_weight mu hmu]
  · simp [highestVector, TorusWeights.highestVector, Pi.single_apply, hx]

theorem highestVector_ne_zero : highestVector mu ≠ 0 :=
  TorusWeights.highestVector_ne_zero (highestBasisIndex mu)

theorem ambientRepresentation_continuous : Continuous (ambientRepresentation mu) :=
  tensorRepresentation_continuous (columnHeight mu)

theorem ambientRepresentation_unitary (U : Matrix.unitaryGroup (Fin d) ℂ) :
    (ambientRepresentation mu U)ᴴ * ambientRepresentation mu U = 1 :=
  tensorRepresentation_unitary (columnHeight mu) U

end FreeEntropy.ExteriorRepresentation
