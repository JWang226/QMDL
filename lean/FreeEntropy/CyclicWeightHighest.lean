/-
Copyright (c) 2026 Free Entropy formalization contributors.
See LICENSE and NOTICE in the repository root for license and attribution.
-/

import FreeEntropy.CartanLieCloning
import FreeEntropy.LiePBWUnique
import FreeEntropy.LiePBWWeights

/-! Genuine highest-line uniqueness and tensor highest-weight support for
cyclic weight models. These discharge the top constituent conditions used
in the cloning construction. -/
noncomputable section
open Matrix
open scoped BigOperators
namespace FreeEntropy.LieMatrixCasimir
variable {d : ℕ} {A : Type*} [Fintype A] [DecidableEq A]

theorem Generators.vector_cyclic_of_column (R : Generators d A) (P : Matrix A Unit ℂ)
    (hP : R.cyclicSpan P = ⊤) : LiePBW.cyclicSpan R (fun a => P a ()) = ⊤ := by
  have hm (X : Matrix A Unit ℂ) (hX : X ∈ R.cyclicSpan P) :
      (fun a => X a ()) ∈ LiePBW.cyclicSpan R (fun a => P a ()) := by
    induction hX using Submodule.span_induction with
    | mem X hX =>
      obtain ⟨w, rfl⟩ := hX
      apply Submodule.subset_span
      exact ⟨w, rfl⟩
    | zero => exact Submodule.zero_mem _
    | add X Y hX hY ihX ihY => exact Submodule.add_mem _ ihX ihY
    | smul c X hX ih => exact Submodule.smul_mem _ c ih
  apply top_unique
  intro v _
  exact hm (fun a _ => v a) (by rw [hP]; trivial)

end FreeEntropy.LieMatrixCasimir

namespace FreeEntropy.CartanLieCloning
open LieMatrixCasimir CasimirWeights
set_option backward.isDefEq.respectTransparency false
variable {d : ℕ} {A B : Type*} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]

def CyclicWeightModel.highestVector (M : CyclicWeightModel d A) : A → ℂ := fun a => M.highest a ()

theorem CyclicWeightModel.vector_cyclic (M : CyclicWeightModel d A) :
    LiePBW.cyclicSpan M.generators M.highestVector = ⊤ :=
  M.generators.vector_cyclic_of_column M.highest M.cyclic

theorem CyclicWeightModel.highestVector_ne_zero [Nonempty A] (M : CyclicWeightModel d A) :
    M.highestVector ≠ 0 := by
  intro hz
  have hc := M.vector_cyclic
  simp [LiePBW.cyclicSpan, hz] at hc

theorem CyclicWeightModel.vector_weight (M : CyclicWeightModel d A) (j : Fin d) :
    M.generators.E j j *ᵥ M.highestVector = (M.row j : ℂ) • M.highestVector := by
  ext a
  exact congrArg (fun X : Matrix A Unit ℂ => X a ()) (M.highest_weight j)

theorem CyclicWeightModel.vector_raise (M : CyclicWeightModel d A) (i j : Fin d) (hij : i < j) :
    M.generators.E i j *ᵥ M.highestVector = 0 := by
  ext a
  exact congrArg (fun X : Matrix A Unit ℂ => X a ()) (M.highest_raise i j hij)

/-- A vector killed by all raising generators belongs to the actual
one-dimensional highest line. -/
theorem CyclicWeightModel.highest_line_unique [Nonempty A] (M : CyclicWeightModel d A)
    (u : A → ℂ) (hu : ∀ i j, i < j → M.generators.E i j *ᵥ u = 0) :
    ∃ c : ℂ, u = c • M.highestVector := by
  apply LiePBW.highest_line_unique M.generators (fun j => (M.row j : ℂ))
    M.highestVector u M.highestVector_ne_zero M.vector_weight M.vector_raise
  · rw [M.vector_cyclic]; trivial
  · exact hu

/-- The highest weight occurs at exactly one coordinate in an actual
orthonormal weight basis. -/
theorem CyclicWeightModel.highest_basis_unique [Nonempty A] (M : CyclicWeightModel d A)
    (a b : A) (ha : M.weight a = M.row) (hb : M.weight b = M.row) : a = b := by
  classical
  have hraise (k : A) (hk : M.weight k = M.row) (i j : Fin d) (hij : i < j) :
      M.generators.E i j *ᵥ Pi.single k (1 : ℂ) = 0 := by
    ext l
    simpa using M.highest_basis_raise k hk i j hij l
  obtain ⟨c, hc⟩ := M.highest_line_unique (Pi.single a 1) (hraise a ha)
  obtain ⟨e, he⟩ := M.highest_line_unique (Pi.single b 1) (hraise b hb)
  by_contra hab
  have hca := congrFun hc a
  have hcb := congrFun hc b
  have heb := congrFun he b
  simp only [Pi.single_eq_same, Pi.smul_apply, smul_eq_mul] at hca heb
  simp only [Pi.single_eq_of_ne (Ne.symm hab), Pi.smul_apply, smul_eq_mul] at hcb
  have hcn : c ≠ 0 := by intro hz; simp [hz] at hca
  have hvb : M.highestVector b = 0 := (mul_eq_zero.mp hcb.symm).resolve_left hcn
  simp [hvb] at heb

/-- Positive root deficits cannot cancel between two tensor factors. -/
theorem CyclicWeightModel.tensor_highest_weights (M : CyclicWeightModel d A)
    (N : CyclicWeightModel d B) (a : A) (b : B)
    (h : M.weight a + N.weight b = M.row + N.row) :
    M.weight a = M.row ∧ N.weight b = N.row := by
  have hz : offset (M.weightCoeff a) + offset (N.weightCoeff b) = 0 := by
    rw [← M.weight_cone a, ← N.weight_cone b]
    funext k
    have hk := congrFun h k
    simp only [Pi.add_apply, Pi.sub_apply, Pi.zero_apply] at *
    linarith
  have hm : M.weightCoeff a = 0 := by
    funext j
    have hp := congrArg (fun v : Fin d → ℝ => ∑ k : Fin d with k.val ≤ j.val, v k) hz
    simp only [Pi.add_apply, Pi.zero_apply, Finset.sum_add_distrib,
      CasimirDecomposition.prefix_offset, Finset.sum_const_zero] at hp
    have hn : (0 : ℝ) ≤ N.weightCoeff b j := Nat.cast_nonneg _
    have hm : (0 : ℝ) ≤ M.weightCoeff a j := Nat.cast_nonneg _
    change M.weightCoeff a j = 0
    exact_mod_cast (show (M.weightCoeff a j : ℝ) = 0 by linarith)
  have he : M.row - M.weight a = 0 := by
    rw [M.weight_cone a, hm]
    funext k
    simp [offset]
  have he' : M.weight a = M.row := (sub_eq_zero.mp he).symm
  refine ⟨he', ?_⟩
  rw [he'] at h
  exact add_left_cancel h

theorem CyclicWeightModel.tensor_highest_basis_unique [Nonempty A] [Nonempty B]
    (M : CyclicWeightModel d A) (N : CyclicWeightModel d B) (a : A) (b : B)
    (h : M.weight a + N.weight b = M.row + N.row) :
    a = M.highestBasis ∧ b = N.highestBasis := by
  obtain ⟨ha, hb⟩ := M.tensor_highest_weights N a b h
  exact ⟨M.highest_basis_unique a M.highestBasis ha M.highestBasis_weight,
    N.highest_basis_unique b N.highestBasis hb N.highestBasis_weight⟩

/-- A nonzero highest vector has the model's prescribed highest weight. -/
theorem CyclicWeightModel.highest_weight_eq [Nonempty A] (M : CyclicWeightModel d A)
    (u : A → ℂ) (hu : u ≠ 0) (lam : Fin d → ℝ)
    (hw : ∀ k, M.generators.E k k *ᵥ u = (lam k : ℂ) • u)
    (hr : ∀ i j, i < j → M.generators.E i j *ᵥ u = 0) : lam = M.row := by
  obtain ⟨c, hc⟩ := M.highest_line_unique u hr
  obtain ⟨a, ha⟩ : ∃ a, u a ≠ 0 := by
    by_contra hn
    push_neg at hn
    exact hu (funext hn)
  have he (k : Fin d) : M.generators.E k k *ᵥ u = (M.row k : ℂ) • u := by
    rw [hc, Matrix.mulVec_smul, M.vector_weight, smul_comm]
  funext k
  apply Complex.ofReal_injective
  apply mul_right_cancel₀ ha
  exact (congrFun ((hw k).symm.trans (he k)) a)

end FreeEntropy.CartanLieCloning
