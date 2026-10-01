/-
Copyright (c) 2026 Free Entropy formalization contributors.
See LICENSE and NOTICE in the repository root for license and attribution.
-/

import FreeEntropy.CartanChoi
import FreeEntropy.CartanChoiMultiplicity
import FreeEntropy.CanonicalCloningSelf

/-! The manuscript's Choi-projector cloner, for the actual canonical modules.
The projector and its multiplicity-one auxiliary representation are constructed,
and the literal Choi contraction is the already proved Cartan channel. -/
noncomputable section
open Matrix
open scoped BigOperators
namespace FreeEntropy.ExteriorRepresentation
open CartanLieCloning CartanChannel CartanChoi
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
variable {d : ℕ}
local instance (mu : Fin d → ℕ) : Nonempty (IrrepIndex mu) :=
  Fin.pos_iff_nonempty.mp (irrep_dimension_pos mu)

def canonicalChoiProjector (mu nu : Fin d → ℕ) (hmu : Antitone mu) (hnu : Antitone nu)
    (hinc : Antitone (fun i => (nu i : ℝ) - (mu i : ℝ))) :
    Matrix (IrrepIndex mu × IrrepIndex nu) (IrrepIndex mu × IrrepIndex nu) ℂ :=
  projector (specifiedCartanEmbedding (canonicalWeightModel mu) (canonicalAuxiliaryModel mu nu)
    (canonicalWeightModel nu) (canonicalAuxiliaryModel_hrow mu nu hmu hnu hinc))

def canonicalChoiEmbedding (mu nu : Fin d → ℕ) (hmu : Antitone mu) (hnu : Antitone nu)
    (hinc : Antitone (fun i => (nu i : ℝ) - (mu i : ℝ))) :
    Matrix (IrrepIndex mu × IrrepIndex nu) (IrrepIndex (auxiliaryRow mu nu)) ℂ :=
  embedding (specifiedCartanEmbedding (canonicalWeightModel mu) (canonicalAuxiliaryModel mu nu)
    (canonicalWeightModel nu) (canonicalAuxiliaryModel_hrow mu nu hmu hnu hinc))

theorem canonicalChoiEmbedding_isometry (mu nu : Fin d → ℕ)
    (hmu : Antitone mu) (hnu : Antitone nu)
    (hinc : Antitone (fun i => (nu i : ℝ) - (mu i : ℝ))) :
    (canonicalChoiEmbedding mu nu hmu hnu hinc)ᴴ * canonicalChoiEmbedding mu nu hmu hnu hinc = 1 :=
  embedding_isometry _ _ _ _ (specifiedCartanEmbedding_isometry _ _ _ _)
    (specifiedCartanEmbedding_intertwines _ _ _ _)

theorem canonicalChoiEmbedding_intertwines (mu nu : Fin d → ℕ)
    (hmu : Antitone mu) (hnu : Antitone nu)
    (hinc : Antitone (fun i => (nu i : ℝ) - (mu i : ℝ))) (i j : Fin d) :
    ((canonicalWeightModel mu).generators.dual.tensor (canonicalWeightModel nu).generators).E i j *
        canonicalChoiEmbedding mu nu hmu hnu hinc =
      canonicalChoiEmbedding mu nu hmu hnu hinc * (canonicalAuxiliaryModel mu nu).generators.E i j :=
  embedding_intertwines _ _ _ _ (specifiedCartanEmbedding_intertwines _ _ _ _) i j

theorem canonicalChoiEmbedding_projector (mu nu : Fin d → ℕ)
    (hmu : Antitone mu) (hnu : Antitone nu)
    (hinc : Antitone (fun i => (nu i : ℝ) - (mu i : ℝ))) :
    canonicalChoiEmbedding mu nu hmu hnu hinc * (canonicalChoiEmbedding mu nu hmu hnu hinc)ᴴ =
      canonicalChoiProjector mu nu hmu hnu hinc := embedding_projector _

theorem canonicalChoiProjector_hermitian (mu nu : Fin d → ℕ)
    (hmu : Antitone mu) (hnu : Antitone nu)
    (hinc : Antitone (fun i => (nu i : ℝ) - (mu i : ℝ))) :
    (canonicalChoiProjector mu nu hmu hnu hinc).IsHermitian := projector_hermitian _

theorem canonicalChoiProjector_idempotent (mu nu : Fin d → ℕ)
    (hmu : Antitone mu) (hnu : Antitone nu)
    (hinc : Antitone (fun i => (nu i : ℝ) - (mu i : ℝ))) :
    canonicalChoiProjector mu nu hmu hnu hinc * canonicalChoiProjector mu nu hmu hnu hinc =
      canonicalChoiProjector mu nu hmu hnu hinc :=
  projector_idempotent _ _ _ _ (specifiedCartanEmbedding_isometry _ _ _ _)
    (specifiedCartanEmbedding_intertwines _ _ _ _)

theorem canonicalChoiProjector_rank (mu nu : Fin d → ℕ)
    (hmu : Antitone mu) (hnu : Antitone nu)
    (hinc : Antitone (fun i => (nu i : ℝ) - (mu i : ℝ))) :
    (canonicalChoiProjector mu nu hmu hnu hinc).rank =
      Fintype.card (IrrepIndex (auxiliaryRow mu nu)) :=
  projector_rank _ _ _ _ (specifiedCartanEmbedding_isometry _ _ _ _)
    (specifiedCartanEmbedding_intertwines _ _ _ _)

/-- The exact multiplicity-one statement defining the relevant PRV copy. -/
theorem canonicalChoi_multiplicity_one (mu nu : Fin d → ℕ)
    (hmu : Antitone mu) (hnu : Antitone nu)
    (hinc : Antitone (fun i => (nu i : ℝ) - (mu i : ℝ))) :
    Module.finrank ℂ (dualEmbeddings (canonicalWeightModel mu) (canonicalAuxiliaryModel mu nu)
      (canonicalWeightModel nu)) = 1 :=
  dualEmbeddings_finrank _ _ _ (canonicalAuxiliaryModel_hrow mu nu hmu hnu hinc)
    (specifiedCartanEmbedding _ _ _ (canonicalAuxiliaryModel_hrow mu nu hmu hnu hinc))
    (specifiedCartanEmbedding_isometry _ _ _ (canonicalAuxiliaryModel_hrow mu nu hmu hnu hinc))
    (specifiedCartanEmbedding_intertwines _ _ _ (canonicalAuxiliaryModel_hrow mu nu hmu hnu hinc))

/-- The constructed range contains the nonzero highest vector of weight ν−μ. -/
theorem canonicalChoi_highest (mu nu : Fin d → ℕ)
    (hmu : Antitone mu) (hnu : Antitone nu)
    (hinc : Antitone (fun i => (nu i : ℝ) - (mu i : ℝ))) :
    ∃ v : IrrepIndex mu × IrrepIndex nu → ℂ, v ≠ 0 ∧
      canonicalChoiProjector mu nu hmu hnu hinc *ᵥ v = v ∧
      (∀ i, ((canonicalWeightModel mu).generators.dual.tensor (canonicalWeightModel nu).generators).E i i *ᵥ v =
        ((nu i : ℂ) - (mu i : ℂ)) • v) ∧
      (∀ i j, i < j → ((canonicalWeightModel mu).generators.dual.tensor (canonicalWeightModel nu).generators).E i j *ᵥ v = 0) := by
  let W := canonicalChoiEmbedding mu nu hmu hnu hinc
  let N := canonicalAuxiliaryModel mu nu
  have hiso : Wᴴ * W = 1 := canonicalChoiEmbedding_isometry mu nu hmu hnu hinc
  have hW := canonicalChoiEmbedding_intertwines mu nu hmu hnu hinc
  refine ⟨W *ᵥ N.highestVector, ?_, ?_, ?_, ?_⟩
  · intro hz
    apply N.highestVector_ne_zero
    have h := congrArg (fun v => Wᴴ *ᵥ v) hz
    simpa only [Matrix.mulVec_mulVec, hiso, Matrix.one_mulVec, Matrix.mulVec_zero] using h
  · rw [← canonicalChoiEmbedding_projector]
    change (W * Wᴴ) *ᵥ (W *ᵥ N.highestVector) = _
    rw [Matrix.mulVec_mulVec, Matrix.mul_assoc, hiso, Matrix.mul_one]
  · intro i
    change _ *ᵥ (W *ᵥ N.highestVector) = _
    rw [Matrix.mulVec_mulVec, hW i i, ← Matrix.mulVec_mulVec, N.vector_weight,
      Matrix.mulVec_smul]
    congr 1
    have he := congrFun (canonicalAuxiliaryModel_row mu nu hinc) i
    change N.row i = _ at he
    exact_mod_cast he
  · intro i j hij
    rw [Matrix.mulVec_mulVec, hW i j, ← Matrix.mulVec_mulVec, N.vector_raise i j hij,
      Matrix.mulVec_zero]

/-- The highest vector generates exactly the Choi projector's range, so the
range is an actual highest-weight irreducible copy, not merely a label. -/
theorem canonicalChoi_cyclic_range (mu nu : Fin d → ℕ)
    (hmu : Antitone mu) (hnu : Antitone nu)
    (hinc : Antitone (fun i => (nu i : ℝ) - (mu i : ℝ))) :
    LiePBW.cyclicSpan
      ((canonicalWeightModel mu).generators.dual.tensor (canonicalWeightModel nu).generators)
      (canonicalChoiEmbedding mu nu hmu hnu hinc *ᵥ (canonicalAuxiliaryModel mu nu).highestVector) =
        LinearMap.range (canonicalChoiEmbedding mu nu hmu hnu hinc).mulVecLin := by
  let W := canonicalChoiEmbedding mu nu hmu hnu hinc
  let N := canonicalAuxiliaryModel mu nu
  have h := LiePBW.map_cyclicSpan N.generators
    ((canonicalWeightModel mu).generators.dual.tensor (canonicalWeightModel nu).generators)
    W.mulVecLin (by
      intro i j x
      change W *ᵥ (N.generators.E i j *ᵥ x) = _ *ᵥ (W *ᵥ x)
      rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, canonicalChoiEmbedding_intertwines]) N.highestVector
  rw [N.vector_cyclic, Submodule.map_top] at h
  exact h.symm

theorem canonicalChoi_projector_range (mu nu : Fin d → ℕ)
    (hmu : Antitone mu) (hnu : Antitone nu)
    (hinc : Antitone (fun i => (nu i : ℝ) - (mu i : ℝ))) :
    LinearMap.range (canonicalChoiProjector mu nu hmu hnu hinc).mulVecLin =
      LinearMap.range (canonicalChoiEmbedding mu nu hmu hnu hinc).mulVecLin := by
  let W := canonicalChoiEmbedding mu nu hmu hnu hinc
  have hW : Wᴴ * W = 1 := canonicalChoiEmbedding_isometry mu nu hmu hnu hinc
  rw [← canonicalChoiEmbedding_projector]
  change LinearMap.range (W * Wᴴ).mulVecLin = LinearMap.range W.mulVecLin
  apply le_antisymm
  · rintro y ⟨x, rfl⟩
    refine ⟨Wᴴ *ᵥ x, ?_⟩
    change W *ᵥ (Wᴴ *ᵥ x) = (W * Wᴴ) *ᵥ x
    rw [Matrix.mulVec_mulVec]
  · rintro y ⟨x, rfl⟩
    refine ⟨W *ᵥ x, ?_⟩
    change (W * Wᴴ) *ᵥ (W *ᵥ x) = W *ᵥ x
    rw [Matrix.mulVec_mulVec, Matrix.mul_assoc, hW, Matrix.mul_one]

/-- Literal Choi matrix of the actual forward channel. -/
theorem canonicalForward_choi (mu nu : Fin d → ℕ)
    (hmu : Antitone mu) (hnu : Antitone nu)
    (hinc : Antitone (fun i => (nu i : ℝ) - (mu i : ℝ))) (hd : 0 < d) :
    choi (canonicalForward mu nu hmu hnu hinc).toFun =
      ((Fintype.card (IrrepIndex mu) : ℝ) / Fintype.card (IrrepIndex (auxiliaryRow mu nu))) •
        canonicalChoiProjector mu nu hmu hnu hinc := by
  have hm : (canonicalForward mu nu hmu hnu hinc).toFun =
      sectorMap (Fintype.card (IrrepIndex mu)) (Fintype.card (IrrepIndex nu))
        (specifiedCartanEmbedding (canonicalWeightModel mu) (canonicalAuxiliaryModel mu nu)
          (canonicalWeightModel nu) (canonicalAuxiliaryModel_hrow mu nu hmu hnu hinc)) := by
    funext X
    rw [canonicalForward_eq_cartan_apply mu nu hmu hnu hinc hd]
    simp only [canonicalCartanForward, specifiedForward, cartanChannel_apply]
  rw [hm]
  exact choi_eq_scaled_projector _

theorem canonicalForward_choiMap (mu nu : Fin d → ℕ)
    (hmu : Antitone mu) (hnu : Antitone nu)
    (hinc : Antitone (fun i => (nu i : ℝ) - (mu i : ℝ))) (hd : 0 < d)
    (X : Matrix (IrrepIndex mu) (IrrepIndex mu) ℂ) :
    choiMap (((Fintype.card (IrrepIndex mu) : ℝ) / Fintype.card (IrrepIndex (auxiliaryRow mu nu))) •
      canonicalChoiProjector mu nu hmu hnu hinc) X = (canonicalForward mu nu hmu hnu hinc).toFun X := by
  rw [← canonicalForward_choi mu nu hmu hnu hinc hd]
  have hm : (canonicalForward mu nu hmu hnu hinc).toFun =
      sectorMap (Fintype.card (IrrepIndex mu)) (Fintype.card (IrrepIndex nu))
        (specifiedCartanEmbedding (canonicalWeightModel mu) (canonicalAuxiliaryModel mu nu)
          (canonicalWeightModel nu) (canonicalAuxiliaryModel_hrow mu nu hmu hnu hinc)) := by
    funext Y
    rw [canonicalForward_eq_cartan_apply mu nu hmu hnu hinc hd]
    simp only [canonicalCartanForward, specifiedForward, cartanChannel_apply]
  rw [hm]
  exact choiMap_sectorMap _ _ _ X

end FreeEntropy.ExteriorRepresentation
