/-
Copyright (c) 2026 Free Entropy formalization contributors.
See LICENSE and NOTICE in the repository root for license and attribution.
-/

import FreeEntropy.CartanReshuffle
import FreeEntropy.CartanHomMultiplicity

/-! Genuine multiplicity one of the auxiliary representation in the Cartan
Choi carrier. Tensor-Hom adjunction identifies its intertwiner space with
the proved one-dimensional Cartan Hom space. -/
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

/-- Maps from the literal dual-source tensor target to the auxiliary model. -/
def dualIntertwiners (M : CyclicWeightModel d A) (N : CyclicWeightModel d B)
    (S : CyclicWeightModel d C) : Submodule ℂ (Matrix B (A × C) ℂ) where
  carrier := {F | ∀ i j, N.generators.E i j * F = F * (M.generators.dual.tensor S.generators).E i j}
  zero_mem' := by simp only [Set.mem_setOf_eq, Matrix.mul_zero, Matrix.zero_mul, implies_true]
  add_mem' := by
    intro F G hF hG i j
    simp only [Matrix.mul_add, Matrix.add_mul, hF i j, hG i j]
  smul_mem' := by
    intro c F hF i j
    simp only [Matrix.mul_smul, Matrix.smul_mul, hF i j]

/-- The tensor-Hom adjunction is an actual complex-linear equivalence. -/
def tensorHomEquiv (M : CyclicWeightModel d A) (N : CyclicWeightModel d B)
    (S : CyclicWeightModel d C) : tensorIntertwiners M N S ≃ₗ[ℂ] dualIntertwiners M N S where
  toFun T := ⟨reshuffle T.val, (reshuffle_intertwines_iff _ _ _ T.val).mp T.property⟩
  invFun F := ⟨unreshuffle F.val, (reshuffle_intertwines_iff _ _ _ _).mpr
    (by simpa only [reshuffle_unreshuffle] using F.property)⟩
  left_inv T := by apply Subtype.ext; rfl
  right_inv F := by apply Subtype.ext; rfl
  map_add' T V := by apply Subtype.ext; rfl
  map_smul' c T := by apply Subtype.ext; rfl

/-- Any auxiliary quotient in the Choi carrier is the reshuffled Cartan map,
up to a scalar. -/
theorem dual_intertwiner_scalar (M : CyclicWeightModel d A) (N : CyclicWeightModel d B)
    (S : CyclicWeightModel d C) (hrow : S.row = M.row + N.row)
    (V : Matrix (A × B) C ℂ) (hViso : Vᴴ * V = 1)
    (hV : ∀ i j, (M.generators.tensor N.generators).E i j * V = V * S.generators.E i j)
    (F : Matrix B (A × C) ℂ)
    (hF : ∀ i j, N.generators.E i j * F = F * (M.generators.dual.tensor S.generators).E i j) :
    ∃ c : ℂ, F = c • reshuffle V := by
  have hT := (reshuffle_intertwines_iff M.generators N.generators S.generators (unreshuffle F)).mpr
    (by simpa only [reshuffle_unreshuffle] using hF)
  obtain ⟨c, hc⟩ := tensor_intertwiner_scalar M N S hrow V hViso hV (unreshuffle F) hT
  exact ⟨c, by simpa only [reshuffle_unreshuffle, reshuffle_smul] using congrArg reshuffle hc⟩

/-- Actual multiplicity one for the auxiliary quotient. -/
theorem dualIntertwiners_finrank (M : CyclicWeightModel d A) (N : CyclicWeightModel d B)
    (S : CyclicWeightModel d C) (hrow : S.row = M.row + N.row)
    (V : Matrix (A × B) C ℂ) (hViso : Vᴴ * V = 1)
    (hV : ∀ i j, (M.generators.tensor N.generators).E i j * V = V * S.generators.E i j) :
    Module.finrank ℂ (dualIntertwiners M N S) = 1 := by
  rw [← (tensorHomEquiv M N S).finrank_eq]
  exact tensorIntertwiners_finrank M N S hrow V hViso hV

/-- Maps embedding the auxiliary model in the dual-source tensor target. -/
def dualEmbeddings (M : CyclicWeightModel d A) (N : CyclicWeightModel d B)
    (S : CyclicWeightModel d C) : Submodule ℂ (Matrix (A × C) B ℂ) where
  carrier := {W | ∀ i j, (M.generators.dual.tensor S.generators).E i j * W = W * N.generators.E i j}
  zero_mem' := by simp only [Set.mem_setOf_eq, Matrix.mul_zero, Matrix.zero_mul, implies_true]
  add_mem' := by
    intro F G hF hG i j
    simp only [Matrix.mul_add, Matrix.add_mul, hF i j, hG i j]
  smul_mem' := by
    intro c F hF i j
    simp only [Matrix.mul_smul, Matrix.smul_mul, hF i j]

theorem dual_intertwiner_adjoint (M : CyclicWeightModel d A) (N : CyclicWeightModel d B)
    (S : CyclicWeightModel d C) (F : Matrix B (A × C) ℂ)
    (hF : F ∈ dualIntertwiners M N S) : Fᴴ ∈ dualEmbeddings M N S := by
  intro i j
  have h := congrArg Matrix.conjTranspose (hF j i)
  simpa only [Matrix.conjTranspose_mul, Generators.adjoint] using h.symm

theorem dual_embedding_adjoint (M : CyclicWeightModel d A) (N : CyclicWeightModel d B)
    (S : CyclicWeightModel d C) (W : Matrix (A × C) B ℂ)
    (hW : W ∈ dualEmbeddings M N S) : Wᴴ ∈ dualIntertwiners M N S := by
  intro i j
  have h := congrArg Matrix.conjTranspose (hW j i)
  simpa only [Matrix.conjTranspose_mul, Generators.adjoint] using h.symm

/-- Every auxiliary copy has exactly the same range as the Choi copy. -/
theorem dual_embedding_scalar (M : CyclicWeightModel d A) (N : CyclicWeightModel d B)
    (S : CyclicWeightModel d C) (hrow : S.row = M.row + N.row)
    (V : Matrix (A × B) C ℂ) (hViso : Vᴴ * V = 1)
    (hV : ∀ i j, (M.generators.tensor N.generators).E i j * V = V * S.generators.E i j)
    (W : Matrix (A × C) B ℂ) (hW : W ∈ dualEmbeddings M N S) :
    ∃ c : ℂ, W = c • (reshuffle V)ᴴ := by
  obtain ⟨c, hc⟩ := dual_intertwiner_scalar M N S hrow V hViso hV Wᴴ
    (dual_embedding_adjoint M N S W hW)
  exact ⟨star c, by simpa only [Matrix.conjTranspose_conjTranspose,
    Matrix.conjTranspose_smul] using congrArg Matrix.conjTranspose hc⟩

/-- The actual auxiliary embedding space is precisely one line. -/
theorem dualEmbeddings_eq_span (M : CyclicWeightModel d A) (N : CyclicWeightModel d B)
    (S : CyclicWeightModel d C) (hrow : S.row = M.row + N.row)
    (V : Matrix (A × B) C ℂ) (hViso : Vᴴ * V = 1)
    (hV : ∀ i j, (M.generators.tensor N.generators).E i j * V = V * S.generators.E i j) :
    dualEmbeddings M N S = Submodule.span ℂ {(reshuffle V)ᴴ} := by
  apply le_antisymm
  · intro W hW
    obtain ⟨c, rfl⟩ := dual_embedding_scalar M N S hrow V hViso hV W hW
    exact Submodule.smul_mem _ c (Submodule.subset_span (Set.mem_singleton _))
  · apply Submodule.span_le.mpr
    intro W hW
    have he := Set.mem_singleton_iff.mp hW
    subst W
    exact dual_intertwiner_adjoint M N S _ ((reshuffle_intertwines_iff _ _ _ V).mp hV)

/-- Literal multiplicity one in the embedding convention used for irreps. -/
theorem dualEmbeddings_finrank (M : CyclicWeightModel d A) (N : CyclicWeightModel d B)
    (S : CyclicWeightModel d C) (hrow : S.row = M.row + N.row)
    (V : Matrix (A × B) C ℂ) (hViso : Vᴴ * V = 1)
    (hV : ∀ i j, (M.generators.tensor N.generators).E i j * V = V * S.generators.E i j) :
    Module.finrank ℂ (dualEmbeddings M N S) = 1 := by
  rw [dualEmbeddings_eq_span M N S hrow V hViso hV]
  apply finrank_span_singleton
  intro hz
  have hf : reshuffle V = 0 := by
    simpa only [Matrix.conjTranspose_conjTranspose, Matrix.conjTranspose_zero] using
      congrArg Matrix.conjTranspose hz
  have hv : V = 0 := congrArg unreshuffle hf
  have hh : (0 : Matrix C C ℂ) = 1 := by
    simpa only [hv, Matrix.conjTranspose_zero, Matrix.zero_mul] using hViso
  exact zero_ne_one hh

end FreeEntropy.CartanChoi
