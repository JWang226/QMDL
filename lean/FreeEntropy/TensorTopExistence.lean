/-
Copyright (c) 2026 Free Entropy formalization contributors.
See LICENSE and NOTICE in the repository root for license and attribution.
-/

import FreeEntropy.CyclicWeightHighest

/-! A complete actual tensor decomposition contains a highest constituent;
its existence follows from the resolution of identity and PBW uniqueness. -/
noncomputable section
open Matrix
open scoped BigOperators Kronecker
namespace FreeEntropy.CartanLieCloning
open LieMatrixCasimir CasimirWeights WeightSectors
set_option backward.isDefEq.respectTransparency false
variable {d : ℕ} {A B : Type*} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]

variable [Nonempty A] [Nonempty B]

def tensorHighestVector (M : CyclicWeightModel d A) (N : CyclicWeightModel d B) : A × B → ℂ :=
  Pi.single (M.highestBasis, N.highestBasis) 1

theorem tensorHighestVector_ne_zero (M : CyclicWeightModel d A) (N : CyclicWeightModel d B) :
    tensorHighestVector M N ≠ 0 := by
  intro hz
  have h := congrFun hz (M.highestBasis, N.highestBasis)
  simp [tensorHighestVector] at h

theorem tensorHighestVector_weight (M : CyclicWeightModel d A) (N : CyclicWeightModel d B)
    (k : Fin d) : (M.generators.tensor N.generators).E k k *ᵥ tensorHighestVector M N =
      ((M.row + N.row) k : ℂ) • tensorHighestVector M N := by
  simp only [Generators.tensor, M.diagonal, N.diagonal, ← totalWeight_diagonal]
  ext ab
  by_cases he : ab = (M.highestBasis, N.highestBasis)
  · subst ab
    simp [tensorHighestVector, weightDiagonal, totalWeight,
      M.highestBasis_weight, N.highestBasis_weight]
  · simp [tensorHighestVector, weightDiagonal, Matrix.mulVec_diagonal, he]

theorem tensorHighestVector_raise (M : CyclicWeightModel d A) (N : CyclicWeightModel d B)
    (i j : Fin d) (hij : i < j) :
    (M.generators.tensor N.generators).E i j *ᵥ tensorHighestVector M N = 0 := by
  ext ab
  simp only [tensorHighestVector, Matrix.mulVec_single_one,
    Matrix.col_apply, Generators.tensor, Matrix.add_apply, Matrix.kronecker_apply]
  change M.generators.E i j ab.1 M.highestBasis * (1 : Matrix B B ℂ) ab.2 N.highestBasis +
    (1 : Matrix A A ℂ) ab.1 M.highestBasis * N.generators.E i j ab.2 N.highestBasis = 0
  rw [M.highest_basis_raise M.highestBasis M.highestBasis_weight i j hij ab.1,
    N.highest_basis_raise N.highestBasis N.highestBasis_weight i j hij ab.2,
    zero_mul, mul_zero, add_zero]

variable {κ : Type*} [Fintype κ] [DecidableEq κ]
  {T : κ → Type*} [∀ i, Fintype (T i)] [∀ i, DecidableEq (T i)]

/-- Some actual constituent sees every nonzero vector of a complete sum. -/
theorem resolution_detects_vector (J : ∀ i, Matrix A (T i) ℂ)
    (hresolve : ∑ i, J i * (J i)ᴴ = 1) (v : A → ℂ) (hv : v ≠ 0) :
    ∃ i, (J i)ᴴ *ᵥ v ≠ 0 := by
  classical
  by_contra hn
  push_neg at hn
  have he := congrArg (fun X : Matrix A A ℂ => X *ᵥ v) hresolve
  dsimp only at he
  rw [Matrix.sum_mulVec, Matrix.one_mulVec] at he
  have hz : (∑ i, (J i * (J i)ᴴ) *ᵥ v) = 0 := by
    apply Finset.sum_eq_zero
    intro i _
    rw [← Matrix.mulVec_mulVec, hn i, Matrix.mulVec_zero]
  exact hv (he.symm.trans hz)

/-- Top weight existence uses the actual sum resolution and the proved
highest-line uniqueness of each constituent. -/
theorem tensor_top_exists [∀ i, Nonempty (T i)]
    (M : CyclicWeightModel d A) (N : CyclicWeightModel d B)
    (S : ∀ i, CyclicWeightModel d (T i)) (J : ∀ i, Matrix (A × B) (T i) ℂ)
    (hresolve : ∑ i, J i * (J i)ᴴ = 1)
    (hJ : ∀ i a b, (M.generators.tensor N.generators).E a b * J i =
      J i * (S i).generators.E a b) : ∃ i, (S i).row = M.row + N.row := by
  obtain ⟨i, hi⟩ := resolution_detects_vector J hresolve (tensorHighestVector M N)
    (tensorHighestVector_ne_zero M N)
  have hadj (a b : Fin d) :
      (S i).generators.E a b * (J i)ᴴ = (J i)ᴴ * (M.generators.tensor N.generators).E a b := by
    have h := congrArg Matrix.conjTranspose (hJ i b a)
    simpa only [Matrix.conjTranspose_mul, Generators.adjoint] using h.symm
  refine ⟨i, (CyclicWeightModel.highest_weight_eq (S i)
    ((J i)ᴴ *ᵥ tensorHighestVector M N) hi (M.row + N.row) ?_ ?_).symm⟩
  · intro k
    rw [Matrix.mulVec_mulVec, hadj, ← Matrix.mulVec_mulVec,
      tensorHighestVector_weight, Matrix.mulVec_smul]
  · intro a b hab
    rw [Matrix.mulVec_mulVec, hadj, ← Matrix.mulVec_mulVec,
      tensorHighestVector_raise M N a b hab, Matrix.mulVec_zero]

end FreeEntropy.CartanLieCloning
