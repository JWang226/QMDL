/-
Copyright (c) 2026 Free Entropy formalization contributors.
See LICENSE and NOTICE in the repository root for license and attribution.
-/

import FreeEntropy.CanonicalCharacterEigen

/-! Exact coefficients of alternants with distinct exponents. -/
noncomputable section
open scoped BigOperators
namespace FreeEntropy.WeylCharacter
open MvPolynomial
set_option backward.isDefEq.respectTransparency false
variable {d : ℕ}

theorem alternant_expansion (a : Fin d → ℕ) :
    alternant a = ∑ e : Equiv.Perm (Fin d),
      Equiv.Perm.sign e • monomial (exponent (fun i => a (e.symm i))) (1 : ℂ) := by
  simp only [alternant, Matrix.det_apply, permuted_power_product]

/-- Each exponent orbit has exactly its determinant sign as coefficient. -/
theorem alternant_coeff_permutation (a : Fin d → ℕ) (ha : Function.Injective a)
    (e : Equiv.Perm (Fin d)) :
    coeff (exponent (fun i => a (e.symm i))) (alternant a) = (Equiv.Perm.sign e : ℤ) := by
  classical
  rw [alternant_expansion, coeff_sum]
  rw [Finset.sum_eq_single e]
  · simp only [Units.smul_def, coeff_smul, coeff_monomial, ite_true]
    simp only [zsmul_eq_mul, mul_one]
  · intro f _ hfe
    have hne : exponent (fun i => a (f.symm i)) ≠ exponent (fun i => a (e.symm i)) := by
      intro h
      apply hfe
      have hh : f.symm = e.symm := by
        apply Equiv.ext
        intro i
        exact ha (congrArg (fun m : Fin d →₀ ℕ => m i) h)
      have heq := congrArg Equiv.symm hh
      simpa only [Equiv.symm_symm] using heq
    simp only [Units.smul_def, coeff_smul, coeff_monomial, if_neg hne, smul_zero]
  · simp

/-- Every nonzero alternant coefficient is on the permutation orbit of its
exponent row. -/
theorem alternant_support_orbit (a : Fin d → ℕ) (m : Fin d →₀ ℕ)
    (hm : coeff m (alternant a) ≠ 0) :
    ∃ e : Equiv.Perm (Fin d), m = exponent (fun i => a (e.symm i)) := by
  classical
  rw [alternant_expansion, coeff_sum] at hm
  obtain ⟨e, _, he⟩ := Finset.exists_ne_zero_of_sum_ne_zero hm
  refine ⟨e, ?_⟩
  by_contra h
  exact he (by simp only [Units.smul_def, coeff_smul, coeff_monomial, if_neg (Ne.symm h), smul_zero])

/-- The ascending exponent row convenient for the sign-free quotient by
our ascending Vandermonde denominator. -/
def ascendingHighest (mu : Fin d → ℕ) : Fin d → ℕ := fun i => mu i.rev + i.val

theorem ascendingHighest_strictMono (mu : Fin d → ℕ) (hmu : Antitone mu) :
    StrictMono (ascendingHighest mu) := by
  intro i j hij
  have hr : j.rev ≤ i.rev := by
    change j.rev.val ≤ i.rev.val
    simp only [Fin.val_rev]
    have hh : i.val < j.val := hij
    omega
  have hm := hmu hr
  change mu i.rev + i.val < mu j.rev + j.val
  have hh : i.val < j.val := hij
  omega

theorem ascendingHighest_reverse (mu : Fin d → ℕ) :
    (fun i => ascendingHighest mu ((Fin.revPerm (n := d)).symm i)) = shiftedHighest mu := by
  funext i
  simp [ascendingHighest, shiftedHighest, Fin.revPerm_symm, Fin.val_rev, Nat.sub_sub, Nat.add_comm]

/-- The target alternant and the denominator have the same highest sign. -/
theorem alternant_highest_coeff (mu : Fin d → ℕ) (hmu : Antitone mu) :
    coeff (exponent (shiftedHighest mu)) (alternant (ascendingHighest mu)) =
      (Equiv.Perm.sign (Fin.revPerm (n := d)) : ℤ) := by
  rw [← ascendingHighest_reverse mu]
  exact alternant_coeff_permutation _ (ascendingHighest_strictMono mu hmu).injective _

theorem denominator_highest_coeff (d : ℕ) :
    coeff (exponent (fun i : Fin d => d - 1 - i.val)) (denominator d) =
      (Equiv.Perm.sign (Fin.revPerm (n := d)) : ℤ) := by
  have h := alternant_coeff_permutation (fun i : Fin d => i.val) Fin.val_injective
    (Fin.revPerm (n := d))
  simpa only [alternant, denominator, Matrix.vandermonde, Fin.revPerm_symm,
    Fin.revPerm_apply, Fin.val_rev, Nat.sub_sub, Nat.add_comm, Matrix.of_apply] using h

end FreeEntropy.WeylCharacter
