/-
Copyright (c) 2026 Free Entropy formalization contributors.
See LICENSE and NOTICE in the repository root for license and attribution.
-/

import FreeEntropy.ExteriorTensorEmbeddingProduct
import FreeEntropy.ExteriorMatrixIrreducible
import FreeEntropy.TensorLieCyclicitySubspace

/-! Canonical polynomial highest-weight irreps are genuine isometric summands
of physical tensor powers, and inherit actual Lie generators and Lie cyclicity. -/
noncomputable section
open Matrix
open scoped BigOperators
namespace FreeEntropy.ExteriorRepresentation
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false

variable {d : ℕ} (mu : Fin d → ℕ)

def tensorDegree : ℕ := ∑ c : Column mu, columnHeight mu c

theorem tensorDegree_eq_sum (hmu : Antitone mu) : tensorDegree mu = ∑ i, mu i := by
  have h := tensor_sum_weight (columnHeight mu)
    (tensorFirst (columnHeight mu) (columnHeight_le mu))
  rw [tensorFirst_weight mu hmu] at h
  exact h.symm

def ambientTensorEmbedding : Matrix (Fin (tensorDegree mu) → Fin d) (AmbientIndex mu) ℂ :=
  exteriorTensorEmbedding (columnHeight mu) d

theorem ambientTensorEmbedding_isometry :
    (ambientTensorEmbedding mu)ᴴ * ambientTensorEmbedding mu = 1 :=
  exteriorTensorEmbedding_isometry _ _

theorem ambientTensorEmbedding_intertwines (U : Matrix.unitaryGroup (Fin d) ℂ) :
    SchurWeyl.physicalRepresentation d (tensorDegree mu) U * ambientTensorEmbedding mu =
      ambientTensorEmbedding mu * ambientRepresentation mu U :=
  exteriorTensorEmbedding_intertwines _ _ U.val

/-- An explicit finite isometry from the constructed canonical irrep into the
actual word space of the physical tensor power. -/
def irrepTensorEmbedding : Matrix (Fin (tensorDegree mu) → Fin d) (IrrepIndex mu) ℂ :=
  ambientTensorEmbedding mu * irrepEmbedding mu

theorem irrepTensorEmbedding_isometry :
    (irrepTensorEmbedding mu)ᴴ * irrepTensorEmbedding mu = 1 := by
  simp only [irrepTensorEmbedding, Matrix.conjTranspose_mul]
  calc
    _ = (irrepEmbedding mu)ᴴ *
        ((ambientTensorEmbedding mu)ᴴ * ambientTensorEmbedding mu) * irrepEmbedding mu := by
      simp only [Matrix.mul_assoc]
    _ = 1 := by rw [ambientTensorEmbedding_isometry, Matrix.mul_one, irrepEmbedding_isometry]

theorem irrepTensorEmbedding_intertwines (U : Matrix.unitaryGroup (Fin d) ℂ) :
    SchurWeyl.physicalRepresentation d (tensorDegree mu) U * irrepTensorEmbedding mu =
      irrepTensorEmbedding mu * irrepMatrix mu U := by
  simp only [irrepTensorEmbedding, ← Matrix.mul_assoc]
  rw [ambientTensorEmbedding_intertwines, Matrix.mul_assoc, irrepEmbedding_intertwines]
  simp only [Matrix.mul_assoc]

/-- Genuine gl(d) generators inherited from the physical tensor action. -/
def irrepGenerators : LieMatrixCasimir.Generators d (IrrepIndex mu) :=
  SchurWeyl.restrictedGenerators (irrepMatrix mu) (irrepTensorEmbedding mu)
    (irrepTensorEmbedding_isometry mu) (irrepTensorEmbedding_intertwines mu)

theorem irrepGenerators_intertwines (i j : Fin d) :
    (TensorPowers.generators d (tensorDegree mu)).E i j * irrepTensorEmbedding mu =
      irrepTensorEmbedding mu * (irrepGenerators mu).E i j :=
  SchurWeyl.restrictedGenerators_intertwines (irrepMatrix mu) (irrepTensorEmbedding mu)
    (irrepTensorEmbedding_isometry mu) (irrepTensorEmbedding_intertwines mu) i j

/-- Every nonzero vector in the constructed canonical irrep is truly Lie-cyclic. -/
theorem irrep_cyclicSpan_eq_top (v : IrrepIndex mu → ℂ) (hv : v ≠ 0) :
    LiePBW.cyclicSpan (irrepGenerators mu) v = ⊤ :=
  SchurWeyl.restricted_cyclicSpan_eq_top (irrepMatrix mu) (irrepTensorEmbedding mu)
    (irrepTensorEmbedding_isometry mu) (irrepTensorEmbedding_intertwines mu)
    (irrepMatrix_irreducible mu) v hv

end FreeEntropy.ExteriorRepresentation
