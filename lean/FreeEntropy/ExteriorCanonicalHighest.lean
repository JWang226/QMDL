/-
Copyright (c) 2026 Free Entropy formalization contributors.
See LICENSE and NOTICE in the repository root for license and attribution.
-/

import FreeEntropy.ExteriorPhysicalIrrep
import FreeEntropy.TensorTorusIntertwiner
import FreeEntropy.HighestWeightDominance

/-! The canonical exterior irrep has the claimed actual Lie highest vector,
proved from its physical tensor inclusion and the exterior basis weights. -/
noncomputable section
open Matrix
open scoped BigOperators
namespace FreeEntropy.ExteriorRepresentation
open UnitaryDecomposition
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

variable {d : ℕ} (mu : Fin d → ℕ)

def ambientGenerators : LieMatrixCasimir.Generators d (AmbientIndex mu) :=
  SchurWeyl.restrictedGenerators (ambientRepresentation mu) (ambientTensorEmbedding mu)
    (ambientTensorEmbedding_isometry mu) (ambientTensorEmbedding_intertwines mu)

theorem ambientGenerators_diagonal (k : Fin d) :
    (ambientGenerators mu).E k k = diagonal (fun b => (tensorWeight (columnHeight mu) b k : ℂ)) := by
  have ht : ∀ z : Fin d → ℂ, (∀ i, ‖z i‖ = 1) →
      TensorPowers.matrix (tensorDegree mu) (diagonal z) * ambientTensorEmbedding mu =
      ambientTensorEmbedding mu * diagonal (fun b =>
        TorusWeights.character z (tensorWeight (columnHeight mu) b)) := by
    intro z hz
    have h := exteriorTensorEmbedding_intertwines (columnHeight mu) d (diagonal z)
    rw [tensorMatrix_diagonal] at h
    exact h
  have h := SchurWeyl.diagonal_intertwines_of_torus (ambientTensorEmbedding mu)
    (tensorWeight (columnHeight mu)) ht k
  change (ambientTensorEmbedding mu)ᴴ * (TensorPowers.generators d (tensorDegree mu)).E k k *
    ambientTensorEmbedding mu = _
  rw [Matrix.mul_assoc, h, ← Matrix.mul_assoc, ambientTensorEmbedding_isometry, Matrix.one_mul]

theorem ambientHighest_weight (k : Fin d) :
    (ambientGenerators mu).E k k *ᵥ (highestVector mu).ofLp =
      (tensorWeight (columnHeight mu) (highestBasisIndex mu) k : ℂ) • (highestVector mu).ofLp := by
  rw [ambientGenerators_diagonal]
  ext b
  by_cases hb : b = highestBasisIndex mu
  · subst b
    simp [highestVector, TorusWeights.highestVector, Matrix.mulVec_diagonal]
  · simp [highestVector, TorusWeights.highestVector, Matrix.mulVec_diagonal, hb]

/-- Raising would strictly decrease the exterior basis energy below its
proved minimum, so it annihilates the actual highest basis vector. -/
theorem ambientHighest_raise (i j : Fin d) (hij : i < j) :
    (ambientGenerators mu).E i j *ᵥ (highestVector mu).ofLp = 0 := by
  let w := (ambientGenerators mu).E i j *ᵥ (highestVector mu).ofLp
  apply funext
  intro b
  by_contra hb
  change w b ≠ 0 at hb
  have he (k : Fin d) :
      (tensorWeight (columnHeight mu) b k : ℂ) =
      (tensorWeight (columnHeight mu) (highestBasisIndex mu) k : ℂ) +
        (if k = i then 1 else 0) - (if k = j then 1 else 0) := by
    have h := congrFun ((ambientGenerators mu).raising_weight
      (fun k => (tensorWeight (columnHeight mu) (highestBasisIndex mu) k : ℂ))
      (highestVector mu).ofLp (ambientHighest_weight mu) i j k) b
    rw [ambientGenerators_diagonal, Matrix.mulVec_diagonal] at h
    change _ * w b = _ * w b at h
    exact mul_right_cancel₀ hb h
  have hr (k : Fin d) :
      (tensorWeight (columnHeight mu) b k : ℝ) =
      (tensorWeight (columnHeight mu) (highestBasisIndex mu) k : ℝ) +
        (if k = i then 1 else 0) - (if k = j then 1 else 0) := by
    have h := congrArg Complex.re (he k)
    simpa only [Complex.add_re, Complex.sub_re, Complex.natCast_re, apply_ite,
      Complex.one_re, Complex.zero_re] using h
  have hsum :
      (∑ k : Fin d, (k.val : ℝ) * tensorWeight (columnHeight mu) b k) =
      (∑ k : Fin d, (k.val : ℝ) * tensorWeight (columnHeight mu) (highestBasisIndex mu) k) +
        (i.val : ℝ) - j.val := by
    simp only [hr, mul_sub, mul_add, Finset.sum_sub_distrib, Finset.sum_add_distrib,
      mul_ite, mul_one, mul_zero]
    simp
  have hmin := tensorEnergy_highest_le (columnHeight mu) (columnHeight_le mu) b
  rw [tensorEnergy_eq_weight_sum, tensorEnergy_eq_weight_sum] at hmin
  have hmin' :
      (∑ k : Fin d, (k.val : ℝ) * tensorWeight (columnHeight mu) (highestBasisIndex mu) k) ≤
      (∑ k : Fin d, (k.val : ℝ) * tensorWeight (columnHeight mu) b k) := by
    exact_mod_cast hmin
  have hij' : (i.val : ℝ) < j.val := by exact_mod_cast hij
  linarith

/-- Coordinates of the actual highest basis vector inside its cyclic irrep. -/
def irrepHighest : IrrepIndex mu → ℂ :=
  (irrepEmbedding mu)ᴴ *ᵥ (highestVector mu).ofLp

theorem irrepEmbedding_highest : irrepEmbedding mu *ᵥ irrepHighest mu = (highestVector mu).ofLp := by
  have hmem : highestVector mu ∈ highestSubspace mu :=
    mem_cyclicSubspace (euclideanRepresentation (ambientRepresentation mu)) (highestVector mu)
  have h := embedding_projection (highestSubspace mu) (highestVector mu)
  rw [Submodule.starProjection_eq_self_iff.mpr hmem] at h
  have he := congrArg WithLp.ofLp h
  simpa only [Matrix.toLpLin_apply, ← Matrix.mulVec_mulVec, irrepHighest, irrepEmbedding] using he

theorem irrepHighest_ne_zero : irrepHighest mu ≠ 0 := by
  intro hz
  have h := irrepEmbedding_highest mu
  rw [hz, Matrix.mulVec_zero] at h
  apply highestVector_ne_zero mu
  exact WithLp.ofLp_injective 2 h.symm

theorem irrepGenerators_compressed (i j : Fin d) :
    (irrepGenerators mu).E i j =
      (irrepEmbedding mu)ᴴ * (ambientGenerators mu).E i j * irrepEmbedding mu := by
  simp only [irrepGenerators, ambientGenerators, SchurWeyl.restrictedGenerators,
    irrepTensorEmbedding, Matrix.conjTranspose_mul, Matrix.mul_assoc]

theorem irrepHighest_weight (hmu : Antitone mu) (k : Fin d) :
    (irrepGenerators mu).E k k *ᵥ irrepHighest mu = (mu k : ℂ) • irrepHighest mu := by
  rw [irrepGenerators_compressed, ← Matrix.mulVec_mulVec, irrepEmbedding_highest,
    ← Matrix.mulVec_mulVec, ambientHighest_weight, Matrix.mulVec_smul]
  simp only [highestBasisIndex, tensorFirst_weight mu hmu]
  rfl

theorem irrepHighest_raise (i j : Fin d) (hij : i < j) :
    (irrepGenerators mu).E i j *ᵥ irrepHighest mu = 0 := by
  rw [irrepGenerators_compressed, ← Matrix.mulVec_mulVec, irrepEmbedding_highest,
    ← Matrix.mulVec_mulVec, ambientHighest_raise mu i j hij, Matrix.mulVec_zero]

theorem irrepHighest_cyclic : LiePBW.cyclicSpan (irrepGenerators mu) (irrepHighest mu) = ⊤ :=
  irrep_cyclicSpan_eq_top mu (irrepHighest mu) (irrepHighest_ne_zero mu)

end FreeEntropy.ExteriorRepresentation
