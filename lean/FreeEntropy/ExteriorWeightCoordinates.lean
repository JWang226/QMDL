/-
Copyright (c) 2026 Free Entropy formalization contributors.
See LICENSE and NOTICE in the repository root for license and attribution.
-/

import FreeEntropy.ExteriorMultiplicity
import FreeEntropy.LieWeightModel
import FreeEntropy.CyclicWeightHighest
import FreeEntropy.CoordinateWeightSpace

/-! Actual orthonormal weight coordinates for the canonical exterior irrep.
Its highest row and integer weights are proved from the literal exterior
embedding, rather than supplied as model fields. -/
noncomputable section
open Matrix
open scoped BigOperators
namespace FreeEntropy.ExteriorRepresentation
open LieMatrixCasimir CartanLieCloning UnitaryDecomposition
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
variable {d : ℕ}

local instance irrepIndex_nonempty (mu : Fin d → ℕ) : Nonempty (IrrepIndex mu) :=
  Fin.pos_iff_nonempty.mp (irrep_dimension_pos mu)

def canonicalWeightCoordinates (mu : Fin d → ℕ) : WeightCoordinates (irrepGenerators mu) :=
  (irrepGenerators mu).weightCoordinates (irrep_cyclicSpan_eq_top mu)

def canonicalWeightModel (mu : Fin d → ℕ) : CyclicWeightModel d (IrrepIndex mu) :=
  (canonicalWeightCoordinates mu).model

def canonicalWeightEmbedding (mu : Fin d → ℕ) : Matrix (AmbientIndex mu) (IrrepIndex mu) ℂ :=
  irrepEmbedding mu * (canonicalWeightCoordinates mu).unitary

theorem canonicalWeightEmbedding_isometry (mu : Fin d → ℕ) :
    (canonicalWeightEmbedding mu)ᴴ * canonicalWeightEmbedding mu = 1 := by
  simp only [canonicalWeightEmbedding, Matrix.conjTranspose_mul, Matrix.mul_assoc,
    ← Matrix.mul_assoc (irrepEmbedding mu)ᴴ (irrepEmbedding mu), irrepEmbedding_isometry,
    Matrix.one_mul, (canonicalWeightCoordinates mu).isometry]

theorem canonicalWeightEmbedding_projection (mu : Fin d → ℕ) :
    canonicalWeightEmbedding mu * (canonicalWeightEmbedding mu)ᴴ =
      irrepEmbedding mu * (irrepEmbedding mu)ᴴ := by
  have hc := mul_eq_one_comm.mp (canonicalWeightCoordinates mu).isometry
  simp only [canonicalWeightEmbedding, Matrix.conjTranspose_mul, Matrix.mul_assoc,
    ← Matrix.mul_assoc (canonicalWeightCoordinates mu).unitary _ _, hc, Matrix.one_mul]

theorem canonicalWeightEmbedding_generators (mu : Fin d → ℕ) (i j : Fin d) :
    (ambientGenerators mu).E i j * canonicalWeightEmbedding mu =
      canonicalWeightEmbedding mu * (canonicalWeightModel mu).generators.E i j := by
  simp only [canonicalWeightEmbedding]
  rw [← Matrix.mul_assoc, irrepEmbedding_lie_intertwines, Matrix.mul_assoc, Matrix.mul_assoc]
  congr 1
  rw [show (canonicalWeightModel mu).generators.E i j =
      (canonicalWeightCoordinates mu).unitaryᴴ * (irrepGenerators mu).E i j *
        (canonicalWeightCoordinates mu).unitary from (canonicalWeightCoordinates mu).generators i j]
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc,
    mul_eq_one_comm.mp (canonicalWeightCoordinates mu).isometry, Matrix.one_mul]

/-- The generic simultaneous diagonalization has exactly the prescribed row. -/
theorem canonicalWeightModel_row (mu : Fin d → ℕ) (hmu : Antitone mu) :
    (canonicalWeightModel mu).row = fun k => (mu k : ℝ) := by
  let C := canonicalWeightCoordinates mu
  let u := C.unitaryᴴ *ᵥ irrepHighest mu
  have hu : u ≠ 0 := by
    intro hz
    have hh := congrArg (fun x => C.unitary *ᵥ x) hz
    apply irrepHighest_ne_zero mu
    simpa only [u, Matrix.mulVec_mulVec, mul_eq_one_comm.mp C.isometry,
      Matrix.one_mulVec, Matrix.mulVec_zero] using hh
  symm
  apply (canonicalWeightModel mu).highest_weight_eq u hu (fun k => (mu k : ℝ))
  · intro k
    rw [show (canonicalWeightModel mu).generators.E k k =
      C.unitaryᴴ * (irrepGenerators mu).E k k * C.unitary from C.generators k k]
    change (_ * _ * _) *ᵥ (C.unitaryᴴ *ᵥ irrepHighest mu) = _
    rw [Matrix.mulVec_mulVec, Matrix.mul_assoc, mul_eq_one_comm.mp C.isometry,
      Matrix.mul_one, ← Matrix.mulVec_mulVec, irrepHighest_weight mu hmu,
      Matrix.mulVec_smul]
    simp only [Complex.ofReal_natCast]
    rfl
  · intro i j hij
    rw [show (canonicalWeightModel mu).generators.E i j =
      C.unitaryᴴ * (irrepGenerators mu).E i j * C.unitary from C.generators i j]
    change (_ * _ * _) *ᵥ (C.unitaryᴴ *ᵥ irrepHighest mu) = _
    rw [Matrix.mulVec_mulVec, Matrix.mul_assoc, mul_eq_one_comm.mp C.isometry,
      Matrix.mul_one, ← Matrix.mulVec_mulVec, irrepHighest_raise mu i j hij,
      Matrix.mulVec_zero]

/-- A nonzero embedding entry has exactly the coordinate's diagonal weight. -/
theorem canonicalWeightEmbedding_weight (mu : Fin d → ℕ)
    (b : AmbientIndex mu) (a : IrrepIndex mu) (hba : canonicalWeightEmbedding mu b a ≠ 0) :
    (canonicalWeightModel mu).weight a = fun k => (tensorWeight (columnHeight mu) b k : ℝ) := by
  funext k
  have h := congrArg (fun M : Matrix (AmbientIndex mu) (IrrepIndex mu) ℂ => M b a)
    (canonicalWeightEmbedding_generators mu k k)
  rw [ambientGenerators_diagonal, (canonicalWeightModel mu).diagonal] at h
  simp only [WeightSectors.weightDiagonal, Matrix.diagonal_mul, Matrix.mul_diagonal] at h
  apply Complex.ofReal_injective
  have he := mul_right_cancel₀ hba (h.trans (mul_comm _ _))
  simpa only [Complex.ofReal_natCast] using he.symm

theorem canonicalWeightEmbedding_column_nonzero (mu : Fin d → ℕ) (a : IrrepIndex mu) :
    ∃ b, canonicalWeightEmbedding mu b a ≠ 0 := by
  by_contra hn
  push_neg at hn
  have h := congrArg (fun M : Matrix (IrrepIndex mu) (IrrepIndex mu) ℂ => M a a)
    (canonicalWeightEmbedding_isometry mu)
  simp [Matrix.mul_apply, hn] at h

/-- A natural occupation chosen from an actual nonzero ambient coordinate. -/
def canonicalWeight (mu : Fin d → ℕ) (a : IrrepIndex mu) : Fin d → ℕ :=
  tensorWeight (columnHeight mu) (canonicalWeightEmbedding_column_nonzero mu a).choose

theorem canonicalWeight_spec (mu : Fin d → ℕ) (a : IrrepIndex mu) :
    (canonicalWeightModel mu).weight a = fun k => (canonicalWeight mu a k : ℝ) :=
  canonicalWeightEmbedding_weight mu _ a (canonicalWeightEmbedding_column_nonzero mu a).choose_spec

theorem canonicalWeightEmbedding_supported (mu : Fin d → ℕ)
    (b : AmbientIndex mu) (a : IrrepIndex mu)
    (hne : tensorWeight (columnHeight mu) b ≠ canonicalWeight mu a) :
    canonicalWeightEmbedding mu b a = 0 := by
  by_contra hb
  apply hne
  have h := (canonicalWeightEmbedding_weight mu b a hb).symm.trans (canonicalWeight_spec mu a)
  funext k
  exact_mod_cast congrFun h k

/-- Every actual weight has the prescribed total polynomial degree. -/
theorem canonicalWeight_sum (mu : Fin d → ℕ) (hmu : Antitone mu) (a : IrrepIndex mu) :
    ∑ k, canonicalWeight mu a k = ∑ k, mu k :=
  weight_total_eq mu hmu _

end FreeEntropy.ExteriorRepresentation
