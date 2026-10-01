/-
Copyright (c) 2026 Free Entropy formalization contributors.
See LICENSE and NOTICE in the repository root for license and attribution.
-/

import FreeEntropy.ExteriorHighestRepresentation

/-! Actual Cartan components of tensor products of the constructed representations. -/
noncomputable section
open Matrix
open scoped BigOperators Kronecker
namespace FreeEntropy.ExteriorRepresentation
open UnitaryDecomposition

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

variable {G H K : Type*} [Group G] [Fintype H] [Fintype K]
  [DecidableEq H] [DecidableEq K]

def pairRepresentation (U : G →* Matrix H H ℂ) (V : G →* Matrix K K ℂ) :
    G →* Matrix (H × K) (H × K) ℂ where
  toFun g := U g ⊗ₖ V g
  map_one' := by simp
  map_mul' g h := by simp only [map_mul, Matrix.mul_kronecker_mul]

theorem pairRepresentation_unitary (U : G →* Matrix H H ℂ) (V : G →* Matrix K K ℂ)
    (hU : ∀ g, (U g)ᴴ * U g = 1) (hV : ∀ g, (V g)ᴴ * V g = 1) (g : G) :
    (pairRepresentation U V g)ᴴ * pairRepresentation U V g = 1 := by
  change (U g ⊗ₖ V g)ᴴ * (U g ⊗ₖ V g) = 1
  rw [Matrix.conjTranspose_kronecker, ← Matrix.mul_kronecker_mul, hU, hV]
  simp

variable {d : ℕ} (mu nu : Fin d → ℕ)

def pairAmbientRepresentation := pairRepresentation (ambientRepresentation mu) (ambientRepresentation nu)

def pairWeight (x : AmbientIndex mu × AmbientIndex nu) : Fin d → ℕ :=
  tensorWeight (columnHeight mu) x.1 + tensorWeight (columnHeight nu) x.2

def highestPair : AmbientIndex mu × AmbientIndex nu := (highestBasisIndex mu, highestBasisIndex nu)

theorem pairWeight_highest (hmu : Antitone mu) (hnu : Antitone nu) :
    pairWeight mu nu (highestPair mu nu) = mu + nu := by
  simp only [pairWeight, highestPair, highestBasisIndex, tensorFirst_weight mu hmu,
    tensorFirst_weight nu hnu]

theorem pairWeight_unique (hmu : Antitone mu) (hnu : Antitone nu)
    (x : AmbientIndex mu × AmbientIndex nu)
    (hx : pairWeight mu nu x = pairWeight mu nu (highestPair mu nu)) : x = highestPair mu nu := by
  rw [pairWeight_highest mu nu hmu hnu] at hx
  have h := pair_weight_unique mu nu hmu hnu x.1 x.2 hx
  exact Prod.ext h.1 h.2

theorem pairAmbient_diagonal (z : Fin d → ℂ) (hz : ∀ i, ‖z i‖ = 1) :
    pairAmbientRepresentation mu nu (Occupation.diagonalUnitary z hz) =
      diagonal (fun x => TorusWeights.character z (pairWeight mu nu x)) := by
  change tensorMatrix (columnHeight mu) (diagonal z) ⊗ₖ
    tensorMatrix (columnHeight nu) (diagonal z) = _
  rw [tensorMatrix_diagonal, tensorMatrix_diagonal, Matrix.diagonal_kronecker_diagonal]
  congr 1
  funext x
  simp only [TorusWeights.character, pairWeight, Pi.add_apply, pow_add, Finset.prod_mul_distrib]

def cartanAmbientSubspace : Submodule ℂ (EuclideanSpace ℂ (AmbientIndex mu × AmbientIndex nu)) :=
  cyclicSubspace (euclideanRepresentation (pairAmbientRepresentation mu nu))
    (TorusWeights.highestVector (highestPair mu nu))

theorem cartanAmbientSubspace_irreducible (hmu : Antitone mu) (hnu : Antitone nu) :
    IrreducibleSubspace (euclideanRepresentation (pairAmbientRepresentation mu nu))
      (cartanAmbientSubspace mu nu) := by
  apply TorusWeights.cyclic_irreducible (pairAmbientRepresentation mu nu)
    (pairRepresentation_unitary _ _ (ambientRepresentation_unitary mu) (ambientRepresentation_unitary nu))
    Occupation.diagonalUnitary (pairWeight mu nu) (pairAmbient_diagonal mu nu)
    (highestPair mu nu) (pairWeight_unique mu nu hmu hnu)

end FreeEntropy.ExteriorRepresentation
