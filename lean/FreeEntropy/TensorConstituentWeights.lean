/-
Copyright (c) 2026 Free Entropy formalization contributors.
See LICENSE and NOTICE in the repository root for license and attribution.
-/

import FreeEntropy.CyclicWeightHighest

/-! Actual tensor constituent embeddings force the highest root cone and
the uniqueness of the top constituent. -/
noncomputable section
open Matrix
open scoped BigOperators
namespace FreeEntropy.CartanLieCloning
open LieMatrixCasimir CasimirWeights WeightSectors
set_option backward.isDefEq.respectTransparency false
variable {d : ℕ} {A B K L : Type*}
  [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
  [Fintype K] [DecidableEq K] [Fintype L] [DecidableEq L]

theorem tensor_intertwiner_weight (M : CyclicWeightModel d A) (N : CyclicWeightModel d B)
    (S : CyclicWeightModel d K) (J : Matrix (A × B) K ℂ)
    (hJ : ∀ i j, (M.generators.tensor N.generators).E i j * J = J * S.generators.E i j)
    (ab : A × B) (k : K) (hnz : J ab k ≠ 0) :
    M.weight ab.1 + N.weight ab.2 = S.weight k := by
  funext i
  have h := congrArg (fun X : Matrix (A × B) K ℂ => X ab k) (hJ i i)
  simp only [Generators.tensor, M.diagonal, N.diagonal, S.diagonal,
    ← totalWeight_diagonal] at h
  change (weightDiagonal (totalWeight M.weight N.weight) i * J) ab k =
    (J * weightDiagonal S.weight i) ab k at h
  simp only [weightDiagonal, Matrix.diagonal_mul, Matrix.mul_diagonal] at h
  apply Complex.ofReal_injective
  exact mul_right_cancel₀ hnz (h.trans (mul_comm _ _))

theorem isometry_column_nonzero (J : Matrix A K ℂ) (hJ : Jᴴ * J = 1) (k : K) :
    ∃ a, J a k ≠ 0 := by
  classical
  by_contra hn
  push_neg at hn
  have h := congrArg (fun X : Matrix K K ℂ => X k k) hJ
  simp [Matrix.mul_apply, hn] at h

/-- Every actual tensor constituent's highest row lies in the proved
positive-root cone beneath the sum of the factor rows. -/
theorem tensor_constituent_highest_cone [Nonempty K]
    (M : CyclicWeightModel d A) (N : CyclicWeightModel d B)
    (S : CyclicWeightModel d K) (J : Matrix (A × B) K ℂ) (hiso : Jᴴ * J = 1)
    (hJ : ∀ i j, (M.generators.tensor N.generators).E i j * J = J * S.generators.E i j) :
    ∃ c : Fin (d - 1) → ℕ, M.row + N.row - S.row = offset c := by
  obtain ⟨ab, hab⟩ := isometry_column_nonzero J hiso S.highestBasis
  have hw := tensor_intertwiner_weight M N S J hJ ab S.highestBasis hab
  rw [S.highestBasis_weight] at hw
  refine ⟨M.weightCoeff ab.1 + N.weightCoeff ab.2, ?_⟩
  rw [LiePBW.offset_add, ← M.weight_cone ab.1, ← N.weight_cone ab.2, ← hw]
  abel

/-- A column of a top constituent is supported only at the tensor of
factor highest coordinates. -/
theorem tensor_top_column_support [Nonempty A] [Nonempty B] [Nonempty K]
    (M : CyclicWeightModel d A) (N : CyclicWeightModel d B)
    (S : CyclicWeightModel d K) (J : Matrix (A × B) K ℂ)
    (hJ : ∀ i j, (M.generators.tensor N.generators).E i j * J = J * S.generators.E i j)
    (htop : S.row = M.row + N.row) (ab : A × B)
    (hab : ab ≠ (M.highestBasis, N.highestBasis)) : J ab S.highestBasis = 0 := by
  by_contra hn
  have hw := tensor_intertwiner_weight M N S J hJ ab S.highestBasis hn
  rw [S.highestBasis_weight, htop] at hw
  obtain ⟨ha, hb⟩ := M.tensor_highest_basis_unique N ab.1 ab.2 hw
  exact hab (Prod.ext ha hb)

/-- Two orthogonal genuine constituents cannot both have the sum of
factor highest weights. This is a proved multiplicity-one statement. -/
theorem tensor_top_not_orthogonal [Nonempty A] [Nonempty B] [Nonempty K] [Nonempty L]
    (M : CyclicWeightModel d A) (N : CyclicWeightModel d B)
    (S : CyclicWeightModel d K) (T : CyclicWeightModel d L)
    (J : Matrix (A × B) K ℂ) (F : Matrix (A × B) L ℂ)
    (hJiso : Jᴴ * J = 1) (hFiso : Fᴴ * F = 1)
    (hJ : ∀ i j, (M.generators.tensor N.generators).E i j * J = J * S.generators.E i j)
    (hF : ∀ i j, (M.generators.tensor N.generators).E i j * F = F * T.generators.E i j)
    (hS : S.row = M.row + N.row) (hT : T.row = M.row + N.row) : Jᴴ * F ≠ 0 := by
  classical
  let ab := (M.highestBasis, N.highestBasis)
  have hJn : J ab S.highestBasis ≠ 0 := by
    obtain ⟨x, hx⟩ := isometry_column_nonzero J hJiso S.highestBasis
    by_cases he : x = ab
    · simpa [he] using hx
    · exact (hx (tensor_top_column_support M N S J hJ hS x he)).elim
  have hFn : F ab T.highestBasis ≠ 0 := by
    obtain ⟨x, hx⟩ := isometry_column_nonzero F hFiso T.highestBasis
    by_cases he : x = ab
    · simpa [he] using hx
    · exact (hx (tensor_top_column_support M N T F hF hT x he)).elim
  intro hz
  have he := congrArg (fun X : Matrix K L ℂ => X S.highestBasis T.highestBasis) hz
  dsimp only at he
  have he' : (Jᴴ * F) S.highestBasis T.highestBasis =
      star (J ab S.highestBasis) * F ab T.highestBasis := by
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply]
    apply Finset.sum_eq_single ab
    · intro x _ hx
      rw [tensor_top_column_support M N S J hJ hS x hx, star_zero, zero_mul]
    · intro hn
      exact (hn (Finset.mem_univ _)).elim
  rw [he', Matrix.zero_apply] at he
  exact (mul_ne_zero (star_ne_zero.mpr hJn) hFn) he

end FreeEntropy.CartanLieCloning
