/-
Copyright (c) 2026 Free Entropy formalization contributors.
See LICENSE and NOTICE in the repository root for license and attribution.
-/

import FreeEntropy.UnitaryDecompositionMatrices
import FreeEntropy.ExteriorHighestRepresentation

/-! Finite unitary matrices for every polynomial highest-weight representation,
constructed from the genuine cyclic exterior-tensor subspace. -/

noncomputable section
open Matrix
open scoped BigOperators
namespace FreeEntropy.ExteriorRepresentation
open UnitaryDecomposition

variable {d : ℕ} (mu : Fin d → ℕ)

abbrev IrrepIndex := Fin (Module.finrank ℂ (highestSubspace mu))

def irrepEmbedding : Matrix (AmbientIndex mu) (IrrepIndex mu) ℂ :=
  embedding (highestSubspace mu)

def irrepMatrix : Matrix.unitaryGroup (Fin d) ℂ →* Matrix (IrrepIndex mu) (IrrepIndex mu) ℂ :=
  restrictedMatrix (ambientRepresentation mu) (highestSubspace mu)
    (highestSubspace_irreducible mu).invariant

theorem irrep_dimension_pos : 0 < Module.finrank ℂ (highestSubspace mu) :=
  Submodule.one_le_finrank_iff.mpr (highestSubspace_irreducible mu).ne_bot

theorem irrepEmbedding_isometry : (irrepEmbedding mu)ᴴ * irrepEmbedding mu = 1 :=
  embedding_isometry (highestSubspace mu)

theorem irrepEmbedding_intertwines (U : Matrix.unitaryGroup (Fin d) ℂ) :
    ambientRepresentation mu U * irrepEmbedding mu = irrepEmbedding mu * irrepMatrix mu U :=
  embedding_intertwines (ambientRepresentation mu) (highestSubspace mu)
    (highestSubspace_irreducible mu).invariant U

theorem irrepMatrix_irreducible :
    Representation.IsIrreducible (Twirling.matrixRepresentation (irrepMatrix mu)) :=
  restrictedMatrix_irreducible (ambientRepresentation mu) (highestSubspace mu) _
    (highestSubspace_irreducible mu).isIrreducible

theorem irrepMatrix_unitary (U : Matrix.unitaryGroup (Fin d) ℂ) :
    (irrepMatrix mu U)ᴴ * irrepMatrix mu U = 1 :=
  restrictedMatrix_unitary (ambientRepresentation mu) (ambientRepresentation_unitary mu)
    (highestSubspace mu) _ U

theorem irrepMatrix_continuous : Continuous (irrepMatrix mu) :=
  restrictedMatrix_continuous (ambientRepresentation mu) (ambientRepresentation_continuous mu)
    (highestSubspace mu) _

end FreeEntropy.ExteriorRepresentation
