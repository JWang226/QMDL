/-
Copyright (c) 2026 Free Entropy formalization contributors.
See LICENSE and NOTICE in the repository root for license and attribution.
-/

import FreeEntropy.WeylDenominator
import FreeEntropy.LieCharacterCanonical

/-! Elementary alternating-polynomial consequences used in the exact
character argument. Repeated-coordinate coefficients vanish in characteristic
zero, and all permuted exponents have the same support status. -/
noncomputable section
open scoped BigOperators
namespace FreeEntropy.WeylCharacter
open MvPolynomial
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
variable {d : ℕ}

/-- Alternation under literal renaming of the variables. -/
def IsAlternating (p : MvPolynomial (Fin d) ℂ) : Prop :=
  ∀ e : Equiv.Perm (Fin d), rename e p = Equiv.Perm.sign e • p

/-- Every literal determinant alternant is alternating in its variables. -/
theorem alternant_alternating (a : Fin d → ℕ) : IsAlternating (alternant a) := by
  intro e
  unfold alternant
  rw [AlgHom.map_det]
  have h := Matrix.det_permute e (fun i j : Fin d => (X i : MvPolynomial (Fin d) ℂ) ^ a j)
  have hmap : (rename e).mapMatrix
      (fun i j : Fin d => (X i : MvPolynomial (Fin d) ℂ) ^ a j) =
      (Matrix.of (fun i j : Fin d => (X i : MvPolynomial (Fin d) ℂ) ^ a j)).submatrix e id := by
    ext i j
    simp [AlgHom.mapMatrix_apply, Matrix.map_apply, Matrix.submatrix_apply]
  rw [hmap]
  simpa only [Units.smul_def, zsmul_eq_mul] using h

theorem denominator_alternating (d : ℕ) : IsAlternating (denominator d) := by
  intro e
  unfold denominator
  rw [AlgHom.map_det]
  have h := Matrix.det_permute e
    (Matrix.vandermonde (fun i : Fin d => (X i : MvPolynomial (Fin d) ℂ)))
  have hmap : (rename e).mapMatrix
      (Matrix.vandermonde (fun i : Fin d => (X i : MvPolynomial (Fin d) ℂ))) =
      (Matrix.vandermonde (fun i : Fin d => (X i : MvPolynomial (Fin d) ℂ))).submatrix e id := by
    ext i j
    simp [AlgHom.mapMatrix_apply, Matrix.map_apply, Matrix.submatrix_apply, Matrix.vandermonde]
  rw [hmap]
  simpa only [Units.smul_def, zsmul_eq_mul] using h

theorem IsAlternating.mul_symmetric {p q : MvPolynomial (Fin d) ℂ}
    (hp : IsAlternating p) (hq : ∀ e : Equiv.Perm (Fin d), rename e q = q) :
    IsAlternating (p * q) := by
  intro e
  rw [map_mul, hp e, hq e]
  simp only [Units.smul_def, zsmul_eq_mul]
  ring

theorem canonical_denominator_character_alternating (mu : Fin d → ℕ) :
    IsAlternating (denominator d * LieCharacter.character (ExteriorRepresentation.canonicalWeight mu)) :=
  (denominator_alternating d).mul_symmetric (ExteriorRepresentation.canonical_character_rename mu)

/-- The signed coefficient relation follows from actual polynomial renaming. -/
theorem IsAlternating.coeff_permutation {p : MvPolynomial (Fin d) ℂ}
    (hp : IsAlternating p) (m : Fin d →₀ ℕ) (e : Equiv.Perm (Fin d)) :
    (Equiv.Perm.sign e : ℤ) • coeff (m.mapDomain e) p = coeff m p := by
  have h := coeff_rename_mapDomain e e.injective p m
  rw [hp e] at h
  simpa only [Units.smul_def, coeff_smul] using h

/-- Permuting coordinates preserves the nonzero coefficient support. -/
theorem IsAlternating.coeff_permutation_ne_zero {p : MvPolynomial (Fin d) ℂ}
    (hp : IsAlternating p) (m : Fin d →₀ ℕ) (e : Equiv.Perm (Fin d)) :
    coeff (m.mapDomain e) p ≠ 0 ↔ coeff m p ≠ 0 := by
  have h := hp.coeff_permutation m e
  rw [← h]
  rw [smul_ne_zero_iff]
  constructor
  · intro hn
    exact ⟨(Equiv.Perm.sign e).ne_zero, hn⟩
  · exact And.right

/-- A swap fixing an exponent reverses its coefficient; hence repeated
coordinates cannot occur in the support of an alternating polynomial. -/
theorem IsAlternating.coeff_eq_zero_of_eq {p : MvPolynomial (Fin d) ℂ}
    (hp : IsAlternating p) (m : Fin d →₀ ℕ) (i j : Fin d)
    (hij : i ≠ j) (hm : m i = m j) : coeff m p = 0 := by
  classical
  have he : m.mapDomain (Equiv.swap i j) = m := by
    ext k
    rw [Finsupp.mapDomain_equiv_apply]
    by_cases hki : k = i
    · subst k; simpa using hm.symm
    · by_cases hkj : k = j
      · subst k; simpa using hm
      · simp [Equiv.swap_apply_of_ne_of_ne hki hkj]
  have h := hp.coeff_permutation m (Equiv.swap i j)
  rw [he, Equiv.Perm.sign_swap hij] at h
  have hh : (2 : ℂ) * coeff m p = 0 := by
    simp only [Units.val_neg, Units.val_one, neg_smul, one_smul] at h
    linear_combination -h
  exact (mul_eq_zero.mp hh).resolve_left (by norm_num)

/-- Every supported exponent has pairwise distinct coordinates. -/
theorem IsAlternating.support_injective {p : MvPolynomial (Fin d) ℂ}
    (hp : IsAlternating p) (m : Fin d →₀ ℕ) (hm : coeff m p ≠ 0) :
    Function.Injective m := by
  intro i j he
  by_contra hij
  exact hm (hp.coeff_eq_zero_of_eq m i j hij he)

/-- An alternating polynomial supported on one permutation orbit is fixed
by one coefficient on that orbit. -/
theorem IsAlternating.ext_of_support_orbit {p q : MvPolynomial (Fin d) ℂ}
    (hp : IsAlternating p) (hq : IsAlternating q) (m₀ : Fin d →₀ ℕ)
    (hps : ∀ m, coeff m p ≠ 0 → ∃ e : Equiv.Perm (Fin d), m = m₀.mapDomain e)
    (hqs : ∀ m, coeff m q ≠ 0 → ∃ e : Equiv.Perm (Fin d), m = m₀.mapDomain e)
    (hbase : coeff m₀ p = coeff m₀ q) : p = q := by
  classical
  ext m
  by_cases hm : ∃ e : Equiv.Perm (Fin d), m = m₀.mapDomain e
  · obtain ⟨e, rfl⟩ := hm
    have hc : (Equiv.Perm.sign e : ℤ) • coeff (m₀.mapDomain e) p =
        (Equiv.Perm.sign e : ℤ) • coeff (m₀.mapDomain e) q := by
      rw [hp.coeff_permutation, hq.coeff_permutation, hbase]
    simp only [zsmul_eq_mul] at hc
    apply mul_left_cancel₀ (show ((Equiv.Perm.sign e : ℤ) : ℂ) ≠ 0 by
      exact_mod_cast (Equiv.Perm.sign e).ne_zero) hc
  · have hzeroP : coeff m p = 0 := by
      by_contra hne
      exact hm (hps m hne)
    have hzeroQ : coeff m q = 0 := by
      by_contra hne
      exact hm (hqs m hne)
    rw [hzeroP, hzeroQ]

end FreeEntropy.WeylCharacter
