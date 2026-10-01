/-
Copyright (c) 2026 Free Entropy formalization contributors.
See LICENSE and NOTICE in the repository root for license and attribution.
-/

import FreeEntropy.WeylDenominator
import Mathlib.RingTheory.MvPolynomial.Homogeneous

/-! Homogeneity isolates the scalar character value in the lowest-degree
coefficient of the translated Weyl numerator. -/
noncomputable section
open scoped BigOperators
namespace FreeEntropy.WeylCharacter
open MvPolynomial
set_option backward.isDefEq.respectTransparency false
variable {d : ℕ}

theorem alternant_homogeneous (a : Fin d → ℕ) :
    (alternant a).IsHomogeneous (∑ i, a i) := by
  classical
  rw [alternant, Matrix.det_apply']
  apply IsHomogeneous.sum
  intro s _
  have hp : (∏ i : Fin d, (X (s i) : MvPolynomial (Fin d) ℂ) ^ a i).IsHomogeneous (∑ i, a i) :=
    IsHomogeneous.prod _ _ a (fun i _ => isHomogeneous_X_pow _ _)
  convert hp.C_mul ((Equiv.Perm.sign s : ℤ) : ℂ) using 1 <;> simp

theorem denominator_homogeneous (d : ℕ) :
    (denominator d).IsHomogeneous (∑ i : Fin d, i.val) := by
  simpa only [denominator, alternant, Matrix.vandermonde] using
    alternant_homogeneous (fun i : Fin d => i.val)

/-- The ascending staircase monomial occurs once with positive sign. -/
theorem denominator_staircase_coeff (d : ℕ) :
    coeff (exponent (fun i : Fin d => i.val)) (denominator d) = 1 := by
  classical
  change coeff _ (alternant (fun i : Fin d => i.val)) = _
  rw [alternant, Matrix.det_apply, MvPolynomial.coeff_sum]
  rw [Finset.sum_eq_single (1 : Equiv.Perm (Fin d))]
  · rw [permuted_power_product]
    simp
  · intro s _ hs
    rw [permuted_power_product, coeff_smul]
    have hn : exponent (fun i : Fin d => (s.symm i).val) ≠ exponent (fun i : Fin d => i.val) := by
      intro he
      apply hs
      ext i
      have h := DFunLike.congr_fun he (s i)
      simpa only [exponent_apply, Equiv.symm_apply_apply, Equiv.Perm.one_apply] using h.symm
    simp [coeff_monomial, hn]
  · intro hn
    exact (hn (Finset.mem_univ _)).elim

/-- In the first homogeneous degree, multiplication only sees the second
factor's constant coefficient. -/
theorem coeff_mul_at_homogeneous_degree (p q : MvPolynomial (Fin d) ℂ)
    (m : Fin d →₀ ℕ) (hp : p.IsHomogeneous m.degree) :
    coeff m (p * q) = coeff m p * coeff 0 q := by
  classical
  rw [coeff_mul]
  apply Finset.sum_eq_single (m, 0)
  · intro x hx hxm
    by_cases hc : coeff x.1 p = 0
    · rw [hc, zero_mul]
    · have hdeg : x.1.degree = m.degree := by
        by_contra hn
        exact hc (hp.coeff_eq_zero hn)
      have he : x.1 + x.2 = m := Finset.mem_antidiagonal.mp hx
      have hd := congrArg Finsupp.degree he
      simp only [map_add, hdeg] at hd
      have hz : x.2.degree = 0 := by omega
      have hx2 : x.2 = 0 := (Finsupp.degree_eq_zero_iff x.2).mp hz
      have hx1 : x.1 = m := by simpa only [hx2, add_zero] using he
      exact (hxm (Prod.ext hx1 hx2)).elim
  · intro hn
    exact (hn (Finset.mem_antidiagonal.mpr (add_zero m))).elim

/-- The chosen lowest-degree coefficient of δ·p is exactly p's constant. -/
theorem denominator_mul_staircase_coeff (p : MvPolynomial (Fin d) ℂ) :
    coeff (exponent (fun i : Fin d => i.val)) (denominator d * p) = coeff 0 p := by
  have hh : (denominator d).IsHomogeneous (exponent (fun i : Fin d => i.val)).degree := by
    simpa only [Finsupp.degree_eq_sum, exponent_apply] using denominator_homogeneous d
  rw [coeff_mul_at_homogeneous_degree _ _ _ hh, denominator_staircase_coeff, one_mul]

end FreeEntropy.WeylCharacter
