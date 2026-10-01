/-
Copyright (c) 2026 Free Entropy formalization contributors.
See LICENSE and NOTICE in the repository root for license and attribution.
-/

import FreeEntropy.ExteriorCanonicalHighest
import FreeEntropy.LieCyclicMaps

/-! The Lie cyclic space of the literal canonical highest basis vector is
exactly its actual unitary orbit subspace. -/
noncomputable section
open Matrix
namespace FreeEntropy
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
namespace LiePBW
variable {d : ℕ} {H K : Type*} [Fintype H] [DecidableEq H] [Fintype K] [DecidableEq K]

theorem map_cyclicSpan (R : LieMatrixCasimir.Generators d H)
    (S : LieMatrixCasimir.Generators d K) (f : (H → ℂ) →ₗ[ℂ] (K → ℂ))
    (hf : ∀ i j x, f (R.E i j *ᵥ x) = S.E i j *ᵥ f x) (v : H → ℂ) :
    (cyclicSpan R v).map f = cyclicSpan S (f v) := by
  apply le_antisymm
  · apply Submodule.map_le_iff_le_comap.mpr
    apply Submodule.span_le.mpr
    rintro _ ⟨w, rfl⟩
    change f (word R w *ᵥ v) ∈ cyclicSpan S (f v)
    rw [intertwiner_word R S f hf]
    exact Submodule.subset_span ⟨w, rfl⟩
  · apply Submodule.span_le.mpr
    rintro _ ⟨w, rfl⟩
    exact ⟨word R w *ᵥ v, Submodule.subset_span ⟨w, rfl⟩,
      intertwiner_word R S f hf w v⟩
end LiePBW

namespace ExteriorRepresentation
variable {d : ℕ} (mu : Fin d → ℕ)

theorem irrepEmbedding_lie_intertwines (i j : Fin d) :
    (ambientGenerators mu).E i j * irrepEmbedding mu =
      irrepEmbedding mu * (irrepGenerators mu).E i j := by
  have hA := SchurWeyl.restrictedGenerators_intertwines (ambientRepresentation mu)
    (ambientTensorEmbedding mu) (ambientTensorEmbedding_isometry mu)
    (ambientTensorEmbedding_intertwines mu) i j
  have hI := irrepGenerators_intertwines mu i j
  have h := congrArg (fun X => (ambientTensorEmbedding mu)ᴴ * X) hI
  change _ = _ at h
  simp only [irrepTensorEmbedding, ← Matrix.mul_assoc] at h
  simpa only [ambientGenerators, SchurWeyl.restrictedGenerators,
    ambientTensorEmbedding_isometry, Matrix.one_mul] using h

theorem ambientHighest_cyclic_range :
    LiePBW.cyclicSpan (ambientGenerators mu) (highestVector mu).ofLp =
      LinearMap.range (Matrix.toLin' (irrepEmbedding mu)) := by
  have h := LiePBW.map_cyclicSpan (irrepGenerators mu) (ambientGenerators mu)
    (Matrix.toLin' (irrepEmbedding mu)) (fun i j x => by
      change irrepEmbedding mu *ᵥ ((irrepGenerators mu).E i j *ᵥ x) =
        (ambientGenerators mu).E i j *ᵥ (irrepEmbedding mu *ᵥ x)
      rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, irrepEmbedding_lie_intertwines])
    (irrepHighest mu)
  rw [irrepHighest_cyclic, Submodule.map_top] at h
  simpa only [Matrix.toLin'_apply, irrepEmbedding_highest] using h.symm

theorem ambientHighest_cyclic :
    LiePBW.cyclicSpan (ambientGenerators mu) (highestVector mu).ofLp =
      (highestSubspace mu).map (EuclideanSpace.equiv (AmbientIndex mu) ℂ).toLinearMap := by
  rw [ambientHighest_cyclic_range]
  apply le_antisymm
  · rintro x ⟨v, rfl⟩
    refine ⟨WithLp.toLp 2 (irrepEmbedding mu *ᵥ v), ?_, rfl⟩
    exact UnitaryDecomposition.embedding_mulVec_mem (highestSubspace mu) v
  · rintro x ⟨v, hv, rfl⟩
    refine ⟨(irrepEmbedding mu)ᴴ *ᵥ v.ofLp, ?_⟩
    have h := UnitaryDecomposition.embedding_projection (highestSubspace mu) v
    rw [Submodule.starProjection_eq_self_iff.mpr hv] at h
    simpa only [Matrix.toLpLin_apply, ← Matrix.mulVec_mulVec] using congrArg WithLp.ofLp h

end ExteriorRepresentation
end FreeEntropy
