/-
Copyright (c) 2026 Free Entropy formalization contributors.
See LICENSE and NOTICE in the repository root for license and attribution.
-/

import FreeEntropy.OccupationRepresentation
import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.LinearAlgebra.UnitaryGroup

/-! Diagonal unitary phases distinguish every actual occupation weight. -/
noncomputable section
open scoped BigOperators
open Matrix
namespace FreeEntropy.Occupation
open WordTypes
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
variable {d n : ℕ}

def character (z : Fin d → ℂ) (a : Occupation d n) : ℂ := ∏ i, z i ^ a.val i

theorem tensor_diagonal (z : Fin d → ℂ) :
    TensorPowers.matrix n (diagonal z) = diagonal (TensorPowers.vector n z) := by
  ext x y
  by_cases h : x = y
  · subst y
    simp [TensorPowers.matrix, TensorPowers.vector]
  · have he : ∃ t, x t ≠ y t := by
      by_contra hn
      push_neg at hn
      exact h (funext hn)
    obtain ⟨t, ht⟩ := he
    rw [Matrix.diagonal_apply_ne _ h]
    exact Finset.prod_eq_zero (Finset.mem_univ t) (by simp [Matrix.diagonal_apply_ne _ ht])

theorem diagonal_intertwines (z : Fin d → ℂ) :
    TensorPowers.matrix n (diagonal z) * basis = basis * diagonal (character (n := n) z) := by
  rw [tensor_diagonal]
  ext w a
  simp only [Matrix.diagonal_mul, Matrix.mul_diagonal]
  by_cases hwa : content w = a.val
  · have he : TensorPowers.vector n z w = character z a := by
      unfold TensorPowers.vector character
      have h : (∏ t, z (w t)) = ∏ i, z i ^ content w i := by
        simpa only [Finset.prod_const, content] using
          (Finset.prod_fiberwise' Finset.univ w z).symm
      simpa only [hwa] using h
    rw [he, mul_comm]
  · simp [basis, hwa]

theorem symmetricMatrix_diagonal (z : Fin d → ℂ) :
    symmetricMatrix (n := n) (diagonal z) = diagonal (character (n := n) z) := by
  rw [symmetricMatrix, Matrix.mul_assoc, diagonal_intertwines, ← Matrix.mul_assoc,
    basis_isometry, Matrix.one_mul]

def diagonalUnitary (z : Fin d → ℂ) (hz : ∀ i, ‖z i‖ = 1) : Matrix.unitaryGroup (Fin d) ℂ :=
  ⟨diagonal z, by
    apply Matrix.mem_unitaryGroup_iff'.mpr
    rw [Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal]
    ext i j
    by_cases hij : i = j
    · subst j
      simp [Complex.conj_mul', hz]
    · simp [hij]⟩

/-- A primitive phase of order n+1 distinguishes all possible occupancies. -/
theorem character_separates (a b : Occupation d n) (hab : a ≠ b) :
    ∃ z : Fin d → ℂ, (∀ i, ‖z i‖ = 1) ∧ character z a ≠ character z b := by
  have he : ∃ i, a.val i ≠ b.val i := by
    by_contra hn
    push_neg at hn
    exact hab (Subtype.ext (funext hn))
  obtain ⟨i, hi⟩ := he
  let ζ := Complex.exp (2 * Real.pi * Complex.I / (n + 1 : ℕ))
  have hζ : IsPrimitiveRoot ζ (n + 1) := Complex.isPrimitiveRoot_exp _ (by omega)
  let z : Fin d → ℂ := Function.update (fun _ => 1) i ζ
  refine ⟨z, ?_, ?_⟩
  · intro j
    by_cases h : j = i
    · subst j
      simpa [z] using hζ.norm'_eq_one (by omega)
    · simp [z, h]
  · have hchar (a : Occupation d n) : character z a = ζ ^ a.val i := by
      unfold character
      rw [Finset.prod_eq_single i]
      · simp [z]
      · intro j _ hji
        simp [z, hji]
      · simp
    rw [hchar, hchar]
    intro h
    have ha : a.val i ≤ n := by
      have h := Finset.single_le_sum (f := a.val) (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
      simpa only [a.property] using h
    have hb : b.val i ≤ n := by
      have h := Finset.single_le_sum (f := b.val) (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
      simpa only [b.property] using h
    exact hi (hζ.pow_inj (by omega) (by omega) h)

/-- Every operator commuting with the actual symmetric U(d) action is diagonal
in the occupation basis. -/
theorem commutant_diagonal (T : Matrix (Occupation d n) (Occupation d n) ℂ)
    (hT : ∀ U : Matrix.unitaryGroup (Fin d) ℂ,
      T * symmetricMatrix (n := n) U.val = symmetricMatrix (n := n) U.val * T) :
    T = diagonal (fun a => T a a) := by
  ext a b
  by_cases hab : a = b
  · subst b; simp
  · obtain ⟨z, hz, hchar⟩ := character_separates a b hab
    have h := congrArg (fun M => M a b) (hT (diagonalUnitary z hz))
    change (T * symmetricMatrix (n := n) (diagonal z)) a b = (symmetricMatrix (n := n) (diagonal z) * T) a b at h
    rw [symmetricMatrix_diagonal, Matrix.mul_diagonal, Matrix.diagonal_mul] at h
    have hzero : T a b * (character z b - character z a) = 0 := by
      rw [mul_sub, h, mul_comm (character z a), sub_self]
    have hne : character z b - character z a ≠ 0 := sub_ne_zero.mpr hchar.symm
    simpa [Matrix.diagonal_apply_ne _ hab] using (mul_eq_zero.mp hzero).resolve_right hne

end FreeEntropy.Occupation
