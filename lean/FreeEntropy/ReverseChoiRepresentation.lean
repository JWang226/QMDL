/-
Copyright (c) 2026 Free Entropy formalization contributors.
See LICENSE and NOTICE in the repository root for license and attribution.
-/

import FreeEntropy.ReverseChoi
import FreeEntropy.LieDualTensor
import FreeEntropy.CanonicalDualCyclicHighest

/-! The reverse Choi range carries the genuine dual auxiliary module. -/
noncomputable section
open Matrix
namespace FreeEntropy.CartanChoi
open LieMatrixCasimir CartanLieCloning
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
variable {d : ℕ} {A B C : Type*} [Fintype A] [DecidableEq A]
  [Fintype B] [DecidableEq B] [Fintype C] [DecidableEq C]

theorem reverseEmbedding_intertwines (M : Generators d A) (N : Generators d B) (S : Generators d C)
    (V : Matrix (A × B) C ℂ)
    (hE : ∀ i j, (M.tensor N).E i j * V = V * S.E i j) (i j : Fin d) :
    (S.dual.tensor M).E i j * reverseEmbedding V = reverseEmbedding V * N.dual.E i j := by
  have hbar (i j : Fin d) :
      (M.tensor S.dual).E i j * (embedding V).map (starRingEnd ℂ) =
        (embedding V).map (starRingEnd ℂ) * N.dual.E i j := by
    have h := conjugate_intertwines N (M.dual.tensor S) (embedding V)
      (embedding_intertwines M N S V hE) i j
    rw [Generators.dual_tensor_E] at h
    simpa only [Generators.tensor, Generators.dual_dual_E] using h
  exact swap_tensor_intertwines M S.dual N.dual _ hbar i j

/-- Transport an actual dual highest generator to the reverse projector range. -/
theorem reverseProjector_highest_cyclic [Nonempty B] [Nonempty C]
    (M : CyclicWeightModel d A) (N : CyclicWeightModel d B) (S : CyclicWeightModel d C)
    (V : Matrix (A × B) C ℂ) (hV : Vᴴ * V = 1)
    (hE : ∀ i j, (M.generators.tensor N.generators).E i j * V = V * S.generators.E i j)
    (lam : Fin d → ℂ) (v : B → ℂ) (hv : v ≠ 0)
    (hw : ∀ i, N.generators.dual.E i i *ᵥ v = lam i • v)
    (hr : ∀ i j, i < j → N.generators.dual.E i j *ᵥ v = 0)
    (hc : LiePBW.cyclicSpan N.generators.dual v = ⊤) :
    ∃ w : C × A → ℂ, w ≠ 0 ∧ reverseProjector V *ᵥ w = w ∧
      (∀ i, (S.generators.dual.tensor M.generators).E i i *ᵥ w = lam i • w) ∧
      (∀ i j, i < j → (S.generators.dual.tensor M.generators).E i j *ᵥ w = 0) ∧
      LiePBW.cyclicSpan (S.generators.dual.tensor M.generators) w =
        LinearMap.range (reverseProjector V).mulVecLin := by
  let J := reverseEmbedding V
  have hiso : Jᴴ * J = 1 := reverseEmbedding_isometry M N S V hV hE
  have hinter := reverseEmbedding_intertwines M.generators N.generators S.generators V hE
  have hproj : J * Jᴴ = reverseProjector V := reverseEmbedding_projector V
  have hrange : LinearMap.range (reverseProjector V).mulVecLin = LinearMap.range J.mulVecLin := by
    rw [← hproj]
    apply le_antisymm
    · rintro y ⟨x, rfl⟩
      refine ⟨Jᴴ *ᵥ x, ?_⟩
      change J *ᵥ (Jᴴ *ᵥ x) = (J * Jᴴ) *ᵥ x
      rw [Matrix.mulVec_mulVec]
    · rintro y ⟨x, rfl⟩
      refine ⟨J *ᵥ x, ?_⟩
      change (J * Jᴴ) *ᵥ (J *ᵥ x) = J *ᵥ x
      rw [Matrix.mulVec_mulVec, Matrix.mul_assoc, hiso, Matrix.mul_one]
  refine ⟨J *ᵥ v, ?_, ?_, ?_, ?_, ?_⟩
  · intro hz
    apply hv
    have h := congrArg (fun w => Jᴴ *ᵥ w) hz
    simpa only [Matrix.mulVec_mulVec, hiso, Matrix.one_mulVec, Matrix.mulVec_zero] using h
  · rw [← hproj, Matrix.mulVec_mulVec, Matrix.mul_assoc, hiso, Matrix.mul_one]
  · intro i
    rw [Matrix.mulVec_mulVec, hinter i i, ← Matrix.mulVec_mulVec, hw, Matrix.mulVec_smul]
  · intro i j hij
    rw [Matrix.mulVec_mulVec, hinter i j, ← Matrix.mulVec_mulVec, hr i j hij, Matrix.mulVec_zero]
  · rw [hrange]
    have h := LiePBW.map_cyclicSpan N.generators.dual
      (S.generators.dual.tensor M.generators) J.mulVecLin (by
        intro i j x
        change J *ᵥ (N.generators.dual.E i j *ᵥ x) = _ *ᵥ (J *ᵥ x)
        rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hinter]) v
    rw [hc, Submodule.map_top] at h
    exact h.symm

end FreeEntropy.CartanChoi

namespace FreeEntropy.ExteriorRepresentation
open CartanChoi CartanLieCloning
set_option backward.isDefEq.respectTransparency false
variable {d : ℕ}
local instance (mu : Fin d → ℕ) : Nonempty (IrrepIndex mu) :=
  Fin.pos_iff_nonempty.mp (irrep_dimension_pos mu)

/-- The actual reverse Choi projector is the highest-weight copy with row
`(mu−nu) ∘ reverse`, the dominant rearrangement used in the manuscript. -/
theorem canonicalReverseChoi_highest_cyclic (mu nu : Fin d → ℕ)
    (hmu : Antitone mu) (hnu : Antitone nu)
    (hinc : Antitone (fun i => (nu i : ℝ) - (mu i : ℝ))) :
    let V := specifiedCartanEmbedding (canonicalWeightModel mu) (canonicalAuxiliaryModel mu nu)
      (canonicalWeightModel nu) (canonicalAuxiliaryModel_hrow mu nu hmu hnu hinc)
    ∃ w : IrrepIndex nu × IrrepIndex mu → ℂ, w ≠ 0 ∧ reverseProjector V *ᵥ w = w ∧
      (∀ i, ((canonicalWeightModel nu).generators.dual.tensor (canonicalWeightModel mu).generators).E i i *ᵥ w =
        ((mu i.rev : ℂ) - (nu i.rev : ℂ)) • w) ∧
      (∀ i j, i < j → ((canonicalWeightModel nu).generators.dual.tensor (canonicalWeightModel mu).generators).E i j *ᵥ w = 0) ∧
      LiePBW.cyclicSpan ((canonicalWeightModel nu).generators.dual.tensor (canonicalWeightModel mu).generators) w =
        LinearMap.range (reverseProjector V).mulVecLin := by
  obtain ⟨v, hv, hw, hr, hc⟩ := canonicalAuxiliary_dual_cyclic_highest mu nu hinc
  exact reverseProjector_highest_cyclic (canonicalWeightModel mu) (canonicalAuxiliaryModel mu nu)
    (canonicalWeightModel nu) _
    (specifiedCartanEmbedding_isometry _ _ _ (canonicalAuxiliaryModel_hrow mu nu hmu hnu hinc))
    (specifiedCartanEmbedding_intertwines _ _ _ (canonicalAuxiliaryModel_hrow mu nu hmu hnu hinc))
    _ v hv hw hr hc

end FreeEntropy.ExteriorRepresentation
