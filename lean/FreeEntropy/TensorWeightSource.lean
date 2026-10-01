/-
Copyright (c) 2026 Free Entropy formalization contributors.
See LICENSE and NOTICE in the repository root for license and attribution.
-/

import FreeEntropy.TensorWeightModel

/-! The constructed natural weight model describes the literal physical
source: its eigenvalues are the exact occupation monomials. -/
noncomputable section
open Matrix
namespace FreeEntropy.SchurWeyl
open Occupation
set_option backward.isDefEq.respectTransparency false
variable {d n : ℕ}

/-- The actual physical sector isometry in its constructed weight basis. -/
def sectorWeightEmbedding (i : Sector d n) :
    Matrix (Fin n → Fin d) (SectorSpace d n i) ℂ :=
  (physicalDecomposition d n).embedding i * sectorWeightUnitary i

theorem sectorWeightEmbedding_isometry (i : Sector d n) :
    (sectorWeightEmbedding i)ᴴ * sectorWeightEmbedding i = 1 := by
  simp only [sectorWeightEmbedding, Matrix.conjTranspose_mul, Matrix.mul_assoc,
    ← Matrix.mul_assoc ((physicalDecomposition d n).embedding i)ᴴ
      ((physicalDecomposition d n).embedding i),
    (physicalDecomposition d n).isometry, Matrix.one_mul, sectorWeightUnitary_isometry]

theorem sectorWeightEmbedding_generators (i : Sector d n) (j k : Fin d) :
    (TensorPowers.generators d n).E j k * sectorWeightEmbedding i =
      sectorWeightEmbedding i * (sectorWeightGenerators i).E j k := by
  let J := (physicalDecomposition d n).embedding i
  let W := sectorWeightUnitary i
  have hE : (TensorPowers.generators d n).E j k * J = J * (sectorGenerators i).E j k :=
    restrictedGenerators_intertwines ((physicalDecomposition d n).representation i)
      J ((physicalDecomposition d n).isometry i) ((physicalDecomposition d n).intertwines i) j k
  change _ * (J * W) = (J * W) * (Wᴴ * (sectorGenerators i).E j k * W)
  rw [← Matrix.mul_assoc, hE]
  simp only [Matrix.mul_assoc, ← Matrix.mul_assoc W Wᴴ,
    show W * Wᴴ = 1 from sectorWeightUnitary_coisometry i, Matrix.one_mul]

/-- Each constructed column is supported on exactly its labelled occupation. -/
theorem sectorWeightEmbedding_supported (i : Sector d n) (a : SectorSpace d n i)
    (w : Fin n → Fin d) (hw : WordTypes.content w ≠ (sectorWeight i a).val) :
    sectorWeightEmbedding i w a = 0 := by
  by_contra hn
  apply hw
  funext j
  have h := congrArg (fun M => M w a) (sectorWeightEmbedding_generators i j j)
  dsimp only at h
  rw [TensorPowers.generators_diagonal, sectorWeightGenerators_diagonal,
    Matrix.diagonal_mul, Matrix.mul_diagonal, mul_comm (sectorWeightEmbedding i w a)] at h
  exact_mod_cast mul_right_cancel₀ hn h

/-- Exact physical diagonal-source action, with no character or spectrum
identification premise. This holds for arbitrary complex diagonal entries. -/
theorem sectorWeightEmbedding_source (i : Sector d n) (z : Fin d → ℂ) :
    TensorPowers.matrix n (Matrix.diagonal z) * sectorWeightEmbedding i =
      sectorWeightEmbedding i * Matrix.diagonal (fun a => character z (sectorWeight i a)) := by
  rw [tensor_diagonal]
  ext w a
  rw [Matrix.diagonal_mul, Matrix.mul_diagonal]
  by_cases hw : WordTypes.content w = (sectorWeight i a).val
  · have ha : ofWord w = sectorWeight i a := Subtype.ext hw
    rw [tensorVector_eq_character, ha, mul_comm]
  · rw [sectorWeightEmbedding_supported i a w hw, mul_zero, zero_mul]

/-- The compressed literal tensor source is diagonal with the actual weight
monomials in the proved unitary coordinates. -/
theorem physical_source_weight_diagonal (i : Sector d n) (z : Fin d → ℂ) :
    (sectorWeightEmbedding i)ᴴ * TensorPowers.matrix n (Matrix.diagonal z) *
      sectorWeightEmbedding i = Matrix.diagonal (fun a => character z (sectorWeight i a)) := by
  rw [Matrix.mul_assoc, sectorWeightEmbedding_source, ← Matrix.mul_assoc,
    sectorWeightEmbedding_isometry, Matrix.one_mul]

/-- The previously constructed physical source block and the exact
occupation-monomial diagonal are related by the constructed unitary. -/
theorem physicalBlock_weight_diagonal (i : Sector d n) (z : Fin d → ℂ) :
    (sectorWeightUnitary i)ᴴ * physicalBlock n (Matrix.diagonal z) i * sectorWeightUnitary i =
      Matrix.diagonal (fun a => character z (sectorWeight i a)) := by
  simpa only [sectorWeightEmbedding, Matrix.conjTranspose_mul, physicalBlock,
    Matrix.mul_assoc] using physical_source_weight_diagonal i z

end FreeEntropy.SchurWeyl
