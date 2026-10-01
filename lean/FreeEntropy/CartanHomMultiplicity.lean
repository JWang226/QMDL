/-
Copyright (c) 2026 Free Entropy formalization contributors.
See LICENSE and NOTICE in the repository root for license and attribution.
-/

import FreeEntropy.TensorConstituentWeights
import FreeEntropy.LieCyclicMaps

/-! The Cartan intertwiner space is genuinely one dimensional. Through
finite tensor-Hom adjunction this gives multiplicity one of the auxiliary
representation in the Choi carrier, without assuming a PRV multiplicity. -/
noncomputable section
open Matrix
open scoped BigOperators
namespace FreeEntropy.LiePBW
open LieMatrixCasimir
set_option backward.isDefEq.respectTransparency false
variable {d : ℕ} {H K : Type*} [Fintype H] [DecidableEq H] [Fintype K] [DecidableEq K]

/-- Intertwiners out of a cyclic module are determined by its cyclic vector. -/
theorem intertwiner_ext_of_cyclic (R : Generators d H) (S : Generators d K)
    (v : H → ℂ) (hcyc : cyclicSpan R v = ⊤)
    (T V : Matrix K H ℂ)
    (hT : ∀ i j, T * R.E i j = S.E i j * T)
    (hV : ∀ i j, V * R.E i j = S.E i j * V)
    (hv : T *ᵥ v = V *ᵥ v) : T = V := by
  have hword (F : Matrix K H ℂ) (hF : ∀ i j, F * R.E i j = S.E i j * F)
      (w : List (Root d)) : F *ᵥ (word R w *ᵥ v) = word S w *ᵥ (F *ᵥ v) := by
    apply intertwiner_word R S (Matrix.toLin' F)
    intro i j x
    change F *ᵥ (R.E i j *ᵥ x) = S.E i j *ᵥ (F *ᵥ x)
    simp only [Matrix.mulVec_mulVec, hF]
  have hw (w : List (Root d)) : T *ᵥ (word R w *ᵥ v) = V *ᵥ (word R w *ᵥ v) := by
    rw [hword T hT, hword V hV, hv]
  have hall (x : H → ℂ) (hx : x ∈ cyclicSpan R v) : T *ᵥ x = V *ᵥ x := by
    induction hx using Submodule.span_induction with
    | mem x hx => obtain ⟨w, rfl⟩ := hx; exact hw w
    | zero => simp only [Matrix.mulVec_zero]
    | add x y hx hy ihx ihy => simp only [Matrix.mulVec_add, ihx, ihy]
    | smul c x hx ih => simp only [Matrix.mulVec_smul, ih]
  apply Matrix.toLin'.injective
  apply LinearMap.ext
  intro x
  exact hall x (hcyc.symm ▸ Submodule.mem_top)

end FreeEntropy.LiePBW

namespace FreeEntropy.CartanLieCloning
open LieMatrixCasimir CasimirWeights WeightSectors
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 700000
set_option linter.unusedSectionVars false
variable {d : ℕ} {A B C : Type*}
  [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
  [Fintype C] [DecidableEq C] [Nonempty A] [Nonempty B] [Nonempty C]

/-- A vector of the tensor highest weight is supported at the unique tensor
of the two highest coordinates. -/
theorem tensor_top_vector_support (M : CyclicWeightModel d A) (N : CyclicWeightModel d B)
    (u : A × B → ℂ)
    (hu : ∀ i, (M.generators.tensor N.generators).E i i *ᵥ u =
      ((M.row + N.row) i : ℂ) • u)
    (ab : A × B) (hab : ab ≠ (M.highestBasis, N.highestBasis)) : u ab = 0 := by
  by_contra hn
  have hw : M.weight ab.1 + N.weight ab.2 = M.row + N.row := by
    funext i
    have he := congrFun (hu i) ab
    simp only [Generators.tensor, M.diagonal, N.diagonal] at he
    rw [← totalWeight_diagonal] at he
    simp only [weightDiagonal, Matrix.mulVec_diagonal, Pi.smul_apply, smul_eq_mul] at he
    exact Complex.ofReal_injective (mul_right_cancel₀ hn he)
  obtain ⟨ha, hb⟩ := M.tensor_highest_basis_unique N ab.1 ab.2 hw
  exact hab (Prod.ext ha hb)

theorem tensor_intertwiner_highest_weight (M : CyclicWeightModel d A)
    (N : CyclicWeightModel d B) (S : CyclicWeightModel d C)
    (hrow : S.row = M.row + N.row) (T : Matrix (A × B) C ℂ)
    (hT : ∀ i j, (M.generators.tensor N.generators).E i j * T = T * S.generators.E i j)
    (i : Fin d) :
    (M.generators.tensor N.generators).E i i *ᵥ (T *ᵥ S.highestVector) =
      ((M.row + N.row) i : ℂ) • (T *ᵥ S.highestVector) := by
  rw [Matrix.mulVec_mulVec, hT, ← Matrix.mulVec_mulVec, S.vector_weight,
    Matrix.mulVec_smul, hrow]

/-- Every Cartan intertwiner is a scalar multiple of any fixed isometric
Cartan inclusion. This is the actual one-dimensional Hom-space statement. -/
theorem tensor_intertwiner_scalar (M : CyclicWeightModel d A) (N : CyclicWeightModel d B)
    (S : CyclicWeightModel d C) (hrow : S.row = M.row + N.row)
    (V : Matrix (A × B) C ℂ) (hViso : Vᴴ * V = 1)
    (hV : ∀ i j, (M.generators.tensor N.generators).E i j * V = V * S.generators.E i j)
    (T : Matrix (A × B) C ℂ)
    (hT : ∀ i j, (M.generators.tensor N.generators).E i j * T = T * S.generators.E i j) :
    ∃ c : ℂ, T = c • V := by
  classical
  let ab : A × B := (M.highestBasis, N.highestBasis)
  let v := V *ᵥ S.highestVector
  let u := T *ᵥ S.highestVector
  have hvs (x : A × B) (hx : x ≠ ab) : v x = 0 :=
    tensor_top_vector_support M N v (tensor_intertwiner_highest_weight M N S hrow V hV) x hx
  have hus (x : A × B) (hx : x ≠ ab) : u x = 0 :=
    tensor_top_vector_support M N u (tensor_intertwiner_highest_weight M N S hrow T hT) x hx
  have hv : v ≠ 0 := by
    intro hz
    have hh := congrArg (fun x => Vᴴ *ᵥ x) hz
    simp only [v, Matrix.mulVec_mulVec, hViso, Matrix.one_mulVec, Matrix.mulVec_zero] at hh
    exact S.highestVector_ne_zero hh
  have hvab : v ab ≠ 0 := by
    intro hz
    apply hv
    funext x
    by_cases hx : x = ab
    · simpa only [hx, Pi.zero_apply] using hz
    · exact hvs x hx
  let c : ℂ := u ab / v ab
  have huv : u = c • v := by
    funext x
    by_cases hx : x = ab
    · subst x
      simp only [Pi.smul_apply, smul_eq_mul, c, div_mul_cancel₀ _ hvab]
    · simp only [Pi.smul_apply, smul_eq_mul, hus x hx, hvs x hx, mul_zero]
  refine ⟨c, LiePBW.intertwiner_ext_of_cyclic S.generators (M.generators.tensor N.generators)
    S.highestVector S.vector_cyclic T (c • V) (fun i j => (hT i j).symm) ?_ ?_⟩
  · intro i j
    rw [Matrix.smul_mul, Matrix.mul_smul, ← hV]
  · simpa only [u, v, Matrix.smul_mulVec] using huv

/-- The actual vector space of Cartan Lie intertwiners. -/
def tensorIntertwiners (M : CyclicWeightModel d A) (N : CyclicWeightModel d B)
    (S : CyclicWeightModel d C) : Submodule ℂ (Matrix (A × B) C ℂ) where
  carrier := {T | ∀ i j, (M.generators.tensor N.generators).E i j * T = T * S.generators.E i j}
  zero_mem' := by simp only [Set.mem_setOf_eq, Matrix.mul_zero, Matrix.zero_mul, implies_true]
  add_mem' := by
    intro T V hT hV i j
    simp only [Matrix.mul_add, Matrix.add_mul, hT i j, hV i j]
  smul_mem' := by
    intro c T hT i j
    simp only [Matrix.mul_smul, Matrix.smul_mul, hT i j]

/-- The Cartan Hom space is exactly the line of the constructed inclusion. -/
theorem tensorIntertwiners_eq_span (M : CyclicWeightModel d A) (N : CyclicWeightModel d B)
    (S : CyclicWeightModel d C) (hrow : S.row = M.row + N.row)
    (V : Matrix (A × B) C ℂ) (hViso : Vᴴ * V = 1)
    (hV : ∀ i j, (M.generators.tensor N.generators).E i j * V = V * S.generators.E i j) :
    tensorIntertwiners M N S = Submodule.span ℂ {V} := by
  apply le_antisymm
  · intro T hT
    obtain ⟨c, rfl⟩ := tensor_intertwiner_scalar M N S hrow V hViso hV T hT
    exact Submodule.smul_mem _ c (Submodule.subset_span (Set.mem_singleton V))
  · apply Submodule.span_le.mpr
    intro T hT
    have he : T = V := Set.mem_singleton_iff.mp hT
    subst T
    exact hV

/-- Literal complex dimension one, not a supplied multiplicity assumption. -/
theorem tensorIntertwiners_finrank (M : CyclicWeightModel d A) (N : CyclicWeightModel d B)
    (S : CyclicWeightModel d C) (hrow : S.row = M.row + N.row)
    (V : Matrix (A × B) C ℂ) (hViso : Vᴴ * V = 1)
    (hV : ∀ i j, (M.generators.tensor N.generators).E i j * V = V * S.generators.E i j) :
    Module.finrank ℂ (tensorIntertwiners M N S) = 1 := by
  rw [tensorIntertwiners_eq_span M N S hrow V hViso hV]
  apply finrank_span_singleton
  intro hz
  have hh : (0 : Matrix C C ℂ) = 1 := by simpa only [hz, Matrix.conjTranspose_zero, Matrix.zero_mul] using hViso
  exact zero_ne_one hh

end FreeEntropy.CartanLieCloning
