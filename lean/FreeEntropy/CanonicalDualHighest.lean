/-
Copyright (c) 2026 Free Entropy formalization contributors.
See LICENSE and NOTICE in the repository root for license and attribution.
-/

import FreeEntropy.LieCharacterCanonical
import FreeEntropy.SignedAuxiliaryModel
import FreeEntropy.LieDual

/-! The reverse Choi carrier has the actual dual auxiliary highest weight.
The lowest coordinate is constructed from proved character permutation
symmetry; its annihilation equations follow from the actual root cone. -/
noncomputable section
open Matrix
open scoped BigOperators
namespace FreeEntropy.CartanLieCloning
open LieMatrixCasimir CasimirWeights
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
set_option linter.unusedSectionVars false
variable {d : ℕ} {A : Type*} [Fintype A] [DecidableEq A] [Nonempty A]

def CyclicWeightModel.ReverseWeightClosed (M : CyclicWeightModel d A) : Prop :=
  ∀ a, ∃ b, M.weight b = fun i => M.weight a i.rev

theorem CyclicWeightModel.reverseWeightClosed_shift (M : CyclicWeightModel d A)
    (hM : M.ReverseWeightClosed) (c : ℝ) : (M.shift c).ReverseWeightClosed := by
  intro a
  obtain ⟨b, hb⟩ := hM a
  refine ⟨b, ?_⟩
  funext i
  simp only [CyclicWeightModel.shift_weight, hb]

theorem CyclicWeightModel.exists_lowest_basis (M : CyclicWeightModel d A)
    (hM : M.ReverseWeightClosed) : ∃ k, M.weight k = fun i => M.row i.rev := by
  obtain ⟨k, hk⟩ := hM M.highestBasis
  exact ⟨k, by simpa only [M.highestBasis_weight] using hk⟩

/-- A lowering entry from the lowest weight would give a negative simple-root
coefficient after reversing coordinates, contradicting the genuine root cone. -/
theorem CyclicWeightModel.lowest_basis_lowering_zero (M : CyclicWeightModel d A)
    (hM : M.ReverseWeightClosed) (k : A) (hk : M.weight k = fun l => M.row l.rev)
    (i j : Fin d) (hji : j < i) (a : A) : M.generators.E i j a k = 0 := by
  by_contra hn
  have hs := generator_weight_shift M.generators M.weight M.diagonal i j (ne_of_gt hji) a k hn
  obtain ⟨b, hb⟩ := hM a
  have he : M.row - M.weight b = fun l =>
      (if l = j.rev then 1 else 0) - (if l = i.rev then 1 else 0) := by
    funext l
    have hh := hs l.rev
    rw [hk] at hh
    simp only [Fin.rev_rev, Fin.rev_eq_iff] at hh
    simp only [Pi.sub_apply, hb]
    linarith
  have hijrev : i.rev < j.rev := Fin.rev_lt_rev.mpr hji
  let cut : Fin (d - 1) := ⟨i.rev.val, by have := j.rev.isLt; change i.rev.val < j.rev.val at hijrev; omega⟩
  have hp := congrArg (fun f : Fin d → ℝ => ∑ l : Fin d with l.val ≤ cut.val, f l)
    (M.weight_cone b)
  dsimp only at hp
  rw [he, CasimirDecomposition.prefix_offset] at hp
  have hnot : ¬ j.rev.val ≤ cut.val := by
    change ¬ j.rev.val ≤ i.rev.val
    exact not_le.mpr hijrev
  have hyes : i.rev.val ≤ cut.val := le_rfl
  simp only [Finset.sum_sub_distrib, Finset.sum_ite_eq', Finset.mem_filter,
    Finset.mem_univ, true_and, hnot, hyes, if_false, if_true, zero_sub] at hp
  have hc := Nat.cast_nonneg (α := ℝ) (M.weightCoeff b cut)
  linarith

/-- The coordinate at the actual lowest weight is a nonzero highest vector
for the contragredient generators, with the reversed negative row. -/
theorem CyclicWeightModel.exists_dual_highest (M : CyclicWeightModel d A)
    (hM : M.ReverseWeightClosed) : ∃ v : A → ℂ, v ≠ 0 ∧
    (∀ i, M.generators.dual.E i i *ᵥ v = (-(M.row i.rev) : ℂ) • v) ∧
    (∀ i j, i < j → M.generators.dual.E i j *ᵥ v = 0) := by
  classical
  obtain ⟨k, hk⟩ := M.exists_lowest_basis hM
  refine ⟨Pi.single k 1, ?_, ?_, ?_⟩
  · intro hz
    have h := congrFun hz k
    exact one_ne_zero (by simpa only [Pi.single_eq_same, Pi.zero_apply] using h)
  · intro i
    change -(M.generators.E i i)ᵀ *ᵥ Pi.single k 1 = _
    rw [M.diagonal]
    ext a
    by_cases ha : a = k
    · subst a
      simp [WeightSectors.weightDiagonal, hk]
    · simp [WeightSectors.weightDiagonal, ha]
  · intro i j hij
    ext a
    have hz := M.lowest_basis_lowering_zero hM k hk j i hij a
    have hadj := congrArg (fun X : Matrix A A ℂ => X k a) (M.generators.adjoint j i)
    simp only [Matrix.conjTranspose_apply] at hadj
    have hzero : M.generators.E i j k a = 0 := by
      rw [← hadj]
      simp only [hz, star_zero]
    simp only [Generators.dual, Matrix.mulVec_single_one, Matrix.col_apply,
      Matrix.neg_apply, Matrix.transpose_apply, hzero, neg_zero, Pi.zero_apply]

end FreeEntropy.CartanLieCloning

namespace FreeEntropy.ExteriorRepresentation
open CartanLieCloning
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
variable {d : ℕ}
local instance dual_hi_nonempty (mu : Fin d → ℕ) : Nonempty (IrrepIndex mu) :=
  Fin.pos_iff_nonempty.mp (irrep_dimension_pos mu)

theorem canonicalWeightModel_reverseWeightClosed (mu : Fin d → ℕ) :
    (canonicalWeightModel mu).ReverseWeightClosed := by
  intro a
  obtain ⟨b, hb⟩ := canonicalWeight_permuted mu a Fin.revPerm
  refine ⟨b, ?_⟩
  funext i
  rw [canonicalWeight_spec mu b, canonicalWeight_spec mu a]
  have hh := congrFun hb i
  simp only [Function.comp_apply, Fin.revPerm_apply] at hh
  dsimp only
  exact_mod_cast hh

theorem canonicalAuxiliaryModel_reverseWeightClosed (mu nu : Fin d → ℕ) :
    (canonicalAuxiliaryModel mu nu).ReverseWeightClosed :=
  (canonicalWeightModel (auxiliaryRow mu nu)).reverseWeightClosed_shift
    (canonicalWeightModel_reverseWeightClosed _) _

/-- The actual reverse auxiliary highest weight is the dominant reverse of
`mu−nu`; arbitrary signed forward increments are included. -/
theorem canonicalAuxiliary_dual_highest (mu nu : Fin d → ℕ)
    (hinc : Antitone (fun i => (nu i : ℝ) - (mu i : ℝ))) :
    ∃ v : IrrepIndex (auxiliaryRow mu nu) → ℂ, v ≠ 0 ∧
    (∀ i, (canonicalAuxiliaryModel mu nu).generators.dual.E i i *ᵥ v =
      ((mu i.rev : ℂ) - (nu i.rev : ℂ)) • v) ∧
    (∀ i j, i < j → (canonicalAuxiliaryModel mu nu).generators.dual.E i j *ᵥ v = 0) := by
  obtain ⟨v, hv, hw, hr⟩ := (canonicalAuxiliaryModel mu nu).exists_dual_highest
    (canonicalAuxiliaryModel_reverseWeightClosed mu nu)
  refine ⟨v, hv, ?_, hr⟩
  intro i
  rw [hw, canonicalAuxiliaryModel_row mu nu hinc]
  congr 1
  simp only [Complex.ofReal_sub, Complex.ofReal_natCast, neg_sub]

theorem reverse_increment_dominant (mu nu : Fin d → ℕ)
    (hinc : Antitone (fun i => (nu i : ℝ) - (mu i : ℝ))) :
    Antitone (fun i : Fin d => (mu i.rev : ℝ) - (nu i.rev : ℝ)) := by
  intro i j hij
  have h := hinc (Fin.rev_le_rev.mpr hij)
  linarith

end FreeEntropy.ExteriorRepresentation
