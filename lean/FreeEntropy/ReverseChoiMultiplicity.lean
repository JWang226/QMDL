/-
Copyright (c) 2026 Free Entropy formalization contributors.
See LICENSE and NOTICE in the repository root for license and attribution.
-/

import FreeEntropy.CartanChoiMultiplicity
import FreeEntropy.ReverseChoiRepresentation
import FreeEntropy.CanonicalReverseChoi

/-! Multiplicity one of the dual auxiliary module in the reverse Choi
carrier. Conjugation and tensor-factor exchange reduce this to the actual
Cartan Hom space, without a supplied multiplicity hypothesis. -/
noncomputable section
open Matrix
namespace FreeEntropy.CartanChoi
open LieMatrixCasimir CartanLieCloning
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
set_option linter.unusedSectionVars false
variable {d : ℕ} {A B C : Type*} [Fintype A] [DecidableEq A]
  [Fintype B] [DecidableEq B] [Fintype C] [DecidableEq C]
  [Nonempty A] [Nonempty B] [Nonempty C]

/-- The reverse carrier contains the actual contragredient auxiliary module. -/
def reverseEmbeddings (M : CyclicWeightModel d A) (N : CyclicWeightModel d B)
    (S : CyclicWeightModel d C) : Submodule ℂ (Matrix (C × A) B ℂ) where
  carrier := {W | ∀ i j, (S.generators.dual.tensor M.generators).E i j * W =
    W * N.generators.dual.E i j}
  zero_mem' := by simp only [Set.mem_setOf_eq, Matrix.mul_zero, Matrix.zero_mul, implies_true]
  add_mem' := by
    intro F G hF hG i j
    simp only [Matrix.mul_add, Matrix.add_mul, hF i j, hG i j]
  smul_mem' := by
    intro c F hF i j
    simp only [Matrix.mul_smul, Matrix.smul_mul, hF i j]

/-- Complex conjugation followed by factor exchange gives a forward copy. -/
theorem reverse_embedding_to_forward
    (M : CyclicWeightModel d A) (N : CyclicWeightModel d B)
    (S : CyclicWeightModel d C) (W : Matrix (C × A) B ℂ)
    (hW : W ∈ reverseEmbeddings M N S) :
    swapRows (W.map (starRingEnd ℂ)) ∈ dualEmbeddings M N S := by
  have hbar (i j : Fin d) :
      (S.generators.tensor M.generators.dual).E i j * W.map (starRingEnd ℂ) =
        W.map (starRingEnd ℂ) * N.generators.E i j := by
    have h := conjugate_intertwines N.generators.dual
      (S.generators.dual.tensor M.generators) W hW i j
    rw [Generators.dual_tensor_E] at h
    simpa only [Generators.tensor, Generators.dual_dual_E] using h
  exact swap_tensor_intertwines S.generators M.generators.dual N.generators _ hbar

/-- The normalized Choi isometry generates the same one-dimensional Hom space. -/
theorem dualEmbeddings_eq_span_embedding
    (M : CyclicWeightModel d A) (N : CyclicWeightModel d B)
    (S : CyclicWeightModel d C) (hrow : S.row = M.row + N.row)
    (V : Matrix (A × B) C ℂ) (hViso : Vᴴ * V = 1)
    (hV : ∀ i j, (M.generators.tensor N.generators).E i j * V = V * S.generators.E i j) :
    dualEmbeddings M N S = Submodule.span ℂ {embedding V} := by
  rw [dualEmbeddings_eq_span M N S hrow V hViso hV]
  have hr : (Real.sqrt ((Fintype.card B : ℝ) / Fintype.card C) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr (div_pos
      (by exact_mod_cast Fintype.card_pos (α := B))
      (by exact_mod_cast Fintype.card_pos (α := C)))).ne'
  have he : embedding V =
      (Real.sqrt ((Fintype.card B : ℝ) / Fintype.card C) : ℂ) • (reshuffle V)ᴴ := by
    ext a b
    simp only [embedding, Matrix.smul_apply, Complex.real_smul, smul_eq_mul]
  rw [he, Submodule.span_singleton_smul_eq (isUnit_iff_ne_zero.mpr hr)]

/-- Every reverse auxiliary copy is the constructed Choi copy up to a scalar. -/
theorem reverse_embedding_scalar
    (M : CyclicWeightModel d A) (N : CyclicWeightModel d B)
    (S : CyclicWeightModel d C) (hrow : S.row = M.row + N.row)
    (V : Matrix (A × B) C ℂ) (hViso : Vᴴ * V = 1)
    (hV : ∀ i j, (M.generators.tensor N.generators).E i j * V = V * S.generators.E i j)
    (W : Matrix (C × A) B ℂ) (hW : W ∈ reverseEmbeddings M N S) :
    ∃ c : ℂ, W = c • reverseEmbedding V := by
  have hF := reverse_embedding_to_forward M N S W hW
  rw [dualEmbeddings_eq_span_embedding M N S hrow V hViso hV] at hF
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hF
  refine ⟨star c, ?_⟩
  ext ca b
  have h := congrArg star (congrFun (congrFun hc ca.swap) b)
  simpa only [swapRows, Matrix.map_apply, starRingEnd_apply, Prod.swap_swap,
    Matrix.smul_apply, smul_eq_mul, star_mul', star_star, reverseEmbedding] using h.symm

/-- The reverse Hom space is exactly the line through its Choi isometry. -/
theorem reverseEmbeddings_eq_span
    (M : CyclicWeightModel d A) (N : CyclicWeightModel d B)
    (S : CyclicWeightModel d C) (hrow : S.row = M.row + N.row)
    (V : Matrix (A × B) C ℂ) (hViso : Vᴴ * V = 1)
    (hV : ∀ i j, (M.generators.tensor N.generators).E i j * V = V * S.generators.E i j) :
    reverseEmbeddings M N S = Submodule.span ℂ {reverseEmbedding V} := by
  apply le_antisymm
  · intro W hW
    obtain ⟨c, rfl⟩ := reverse_embedding_scalar M N S hrow V hViso hV W hW
    exact Submodule.smul_mem _ c (Submodule.subset_span (Set.mem_singleton _))
  · apply Submodule.span_le.mpr
    intro W hW
    have he := Set.mem_singleton_iff.mp hW
    subst W
    exact reverseEmbedding_intertwines M.generators N.generators S.generators V hV

/-- Literal multiplicity one of the dual auxiliary representation. -/
theorem reverseEmbeddings_finrank
    (M : CyclicWeightModel d A) (N : CyclicWeightModel d B)
    (S : CyclicWeightModel d C) (hrow : S.row = M.row + N.row)
    (V : Matrix (A × B) C ℂ) (hViso : Vᴴ * V = 1)
    (hV : ∀ i j, (M.generators.tensor N.generators).E i j * V = V * S.generators.E i j) :
    Module.finrank ℂ (reverseEmbeddings M N S) = 1 := by
  rw [reverseEmbeddings_eq_span M N S hrow V hViso hV]
  apply finrank_span_singleton
  intro hz
  have hh := reverseEmbedding_isometry M N S V hViso hV
  rw [hz, Matrix.conjTranspose_zero, Matrix.zero_mul] at hh
  exact zero_ne_one hh

/-- Multiplicity one makes the reverse support projector independent of the
chosen isometric realization of its auxiliary type. -/
theorem reverseProjector_unique
    (M : CyclicWeightModel d A) (N : CyclicWeightModel d B)
    (S : CyclicWeightModel d C) (hrow : S.row = M.row + N.row)
    (V : Matrix (A × B) C ℂ) (hViso : Vᴴ * V = 1)
    (hV : ∀ i j, (M.generators.tensor N.generators).E i j * V = V * S.generators.E i j)
    (W : Matrix (C × A) B ℂ) (hWiso : Wᴴ * W = 1)
    (hW : W ∈ reverseEmbeddings M N S) : W * Wᴴ = reverseProjector V := by
  obtain ⟨c, hc⟩ := reverse_embedding_scalar M N S hrow V hViso hV W hW
  have hJ := reverseEmbedding_isometry M N S V hViso hV
  have hp : c * star c = 1 := by
    rw [hc, Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
      hJ] at hWiso
    have he := congrArg (fun X : Matrix B B ℂ => X N.highestBasis N.highestBasis) hWiso
    simpa only [Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one, one_mul, mul_comm] using he
  rw [hc, Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
    hp, one_smul, reverseEmbedding_projector]

end FreeEntropy.CartanChoi

namespace FreeEntropy.ExteriorRepresentation
open CartanLieCloning CartanChoi
set_option backward.isDefEq.respectTransparency false
variable {d : ℕ}
local instance (mu : Fin d → ℕ) : Nonempty (IrrepIndex mu) :=
  Fin.pos_iff_nonempty.mp (irrep_dimension_pos mu)

/-- The reverse PRV carrier contains its dual auxiliary type exactly once. -/
theorem canonicalReverseChoi_multiplicity_one (mu nu : Fin d → ℕ)
    (hmu : Antitone mu) (hnu : Antitone nu)
    (hinc : Antitone (fun i => (nu i : ℝ) - (mu i : ℝ))) :
    Module.finrank ℂ (reverseEmbeddings (canonicalWeightModel mu)
      (canonicalAuxiliaryModel mu nu) (canonicalWeightModel nu)) = 1 :=
  reverseEmbeddings_finrank _ _ _ (canonicalAuxiliaryModel_hrow mu nu hmu hnu hinc)
    (specifiedCartanEmbedding _ _ _ (canonicalAuxiliaryModel_hrow mu nu hmu hnu hinc))
    (specifiedCartanEmbedding_isometry _ _ _ (canonicalAuxiliaryModel_hrow mu nu hmu hnu hinc))
    (specifiedCartanEmbedding_intertwines _ _ _ (canonicalAuxiliaryModel_hrow mu nu hmu hnu hinc))

/-- Every embedding of the actual dual auxiliary module is the constructed
reverse Choi isometry, up to one scalar. -/
theorem canonicalReverseChoi_embedding_unique (mu nu : Fin d → ℕ)
    (hmu : Antitone mu) (hnu : Antitone nu)
    (hinc : Antitone (fun i => (nu i : ℝ) - (mu i : ℝ)))
    (W : Matrix (IrrepIndex nu × IrrepIndex mu) (IrrepIndex (auxiliaryRow mu nu)) ℂ)
    (hW : W ∈ reverseEmbeddings (canonicalWeightModel mu)
      (canonicalAuxiliaryModel mu nu) (canonicalWeightModel nu)) :
    ∃ c : ℂ, W = c • canonicalReverseChoiEmbedding mu nu hmu hnu hinc :=
  reverse_embedding_scalar _ _ _ (canonicalAuxiliaryModel_hrow mu nu hmu hnu hinc)
    (specifiedCartanEmbedding _ _ _ (canonicalAuxiliaryModel_hrow mu nu hmu hnu hinc))
    (specifiedCartanEmbedding_isometry _ _ _ (canonicalAuxiliaryModel_hrow mu nu hmu hnu hinc))
    (specifiedCartanEmbedding_intertwines _ _ _ (canonicalAuxiliaryModel_hrow mu nu hmu hnu hinc)) W hW

/-- The reverse PRV projector is the unique orthogonal projection obtained from
an isometric copy of the dual auxiliary representation. -/
theorem canonicalReverseChoiProjector_unique (mu nu : Fin d → ℕ)
    (hmu : Antitone mu) (hnu : Antitone nu)
    (hinc : Antitone (fun i => (nu i : ℝ) - (mu i : ℝ)))
    (W : Matrix (IrrepIndex nu × IrrepIndex mu) (IrrepIndex (auxiliaryRow mu nu)) ℂ)
    (hWiso : Wᴴ * W = 1)
    (hW : W ∈ reverseEmbeddings (canonicalWeightModel mu)
      (canonicalAuxiliaryModel mu nu) (canonicalWeightModel nu)) :
    W * Wᴴ = canonicalReverseChoiProjector mu nu hmu hnu hinc :=
  reverseProjector_unique _ _ _ (canonicalAuxiliaryModel_hrow mu nu hmu hnu hinc)
    (specifiedCartanEmbedding _ _ _ (canonicalAuxiliaryModel_hrow mu nu hmu hnu hinc))
    (specifiedCartanEmbedding_isometry _ _ _ (canonicalAuxiliaryModel_hrow mu nu hmu hnu hinc))
    (specifiedCartanEmbedding_intertwines _ _ _ (canonicalAuxiliaryModel_hrow mu nu hmu hnu hinc))
    W hWiso hW

end FreeEntropy.ExteriorRepresentation
