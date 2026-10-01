/-
Copyright (c) 2026 Free Entropy formalization contributors.
See LICENSE and NOTICE in the repository root for license and attribution.
-/

import FreeEntropy.TensorPowers
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.Matrix.PosDef

/-!
# Every rank-one density matrix is a normalized pure state

The spectral theorem and the actual matrix rank show that exactly one
eigenvalue is nonzero. Trace one makes it one; its unitary eigenvector
column gives the normalized vector. No factorization is assumed.
-/

noncomputable section
open scoped BigOperators ComplexOrder
open Matrix

namespace FreeEntropy.RankOneStates

variable {H : Type*} [Fintype H] [DecidableEq H]

theorem exists_normalized_vector_of_hermitian (ρ : Matrix H H ℂ)
    (hρ : ρ.IsHermitian) (ht : ρ.trace = 1) (hr : ρ.rank = 1) :
    ∃ z : H → ℂ, (∑ i, Complex.normSq (z i)) = 1 ∧ ρ = TensorPowers.pure z := by
  classical
  have hc : Fintype.card {i // hρ.eigenvalues i ≠ 0} = 1 := by
    rw [← hρ.rank_eq_card_non_zero_eigs, hr]
  obtain ⟨j, hj⟩ := Fintype.card_eq_one_iff.mp hc
  have hezero (i : H) (hi : i ≠ j.val) : hρ.eigenvalues i = 0 := by
    by_contra hn
    have he := congrArg Subtype.val (hj ⟨i, hn⟩)
    exact hi he
  have hone : (hρ.eigenvalues j.val : ℂ) = 1 := by
    have he := hρ.trace_eq_sum_eigenvalues
    rw [ht, Finset.sum_eq_single j.val] at he
    · exact he.symm
    · intro i _ hi
      simp [hezero i hi]
    · simp
  have heig (i : H) : (hρ.eigenvalues i : ℂ) = if i = j.val then 1 else 0 := by
    by_cases hi : i = j.val
    · simpa only [hi, if_true] using hone
    · simp [hi, hezero i hi]
  let U : Matrix H H ℂ := hρ.eigenvectorUnitary
  let z : H → ℂ := fun i => U i j.val
  have heq : ρ = TensorPowers.pure z := by
    rw [hρ.spectral_theorem, Unitary.conjStarAlgAut_apply]
    change U * diagonal (fun i => (hρ.eigenvalues i : ℂ)) * Uᴴ = TensorPowers.pure z
    ext a b
    simp only [Matrix.mul_apply,
      heig, Matrix.conjTranspose_apply, TensorPowers.pure, z, U]
    simp [Matrix.diagonal_apply]
  refine ⟨z, ?_, heq⟩
  have hnorm := congrArg Complex.re ht
  rw [heq] at hnorm
  simpa only [TensorPowers.pure, Matrix.trace, Matrix.diag, Complex.re_sum,
    Complex.star_def, Complex.mul_conj, Complex.ofReal_re, Complex.one_re] using hnorm

/-- A rank-one positive trace-one matrix supplies the actual normalized
vector required by the fully constructed pure-tensor compression theorem. -/
theorem exists_normalized_vector (ρ : Matrix H H ℂ)
    (hρ : ρ.PosSemidef) (ht : ρ.trace = 1) (hr : ρ.rank = 1) :
    ∃ z : H → ℂ, (∑ i, Complex.normSq (z i)) = 1 ∧ ρ = TensorPowers.pure z :=
  exists_normalized_vector_of_hermitian ρ hρ.isHermitian ht hr

end FreeEntropy.RankOneStates
