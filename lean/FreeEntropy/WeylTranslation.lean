/-
Copyright (c) 2026 Free Entropy formalization contributors.
See LICENSE and NOTICE in the repository root for license and attribution.
-/

import FreeEntropy.WeylDenominator
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.Algebra.Polynomial.Coeff

/-! Polynomial translation and coefficient extraction replace analytic
limits at the identity in the Weyl dimension calculation. -/
noncomputable section
open scoped BigOperators
namespace FreeEntropy.WeylCharacter
open MvPolynomial
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
variable {d : ℕ}

def translate : MvPolynomial (Fin d) ℂ →ₐ[ℂ] MvPolynomial (Fin d) ℂ :=
  MvPolynomial.aeval (fun i => X i + 1)

@[simp] theorem translate_X (i : Fin d) : translate (X i) = X i + (1 : MvPolynomial (Fin d) ℂ) := by
  simp [translate]

@[simp] theorem translate_C (c : ℂ) : translate (C c : MvPolynomial (Fin d) ℂ) = C c := by
  simp [translate]

theorem translate_denominator (d : ℕ) : translate (denominator d) = denominator d := by
  rw [denominator_product]
  simp only [map_prod, map_sub, translate_X, add_sub_add_right_eq_sub]

theorem translate_monomial (a : Fin d →₀ ℕ) (c : ℂ) :
    translate (monomial a c) = C c * ∏ i : Fin d, (X i + 1) ^ a i := by
  rw [monomial_eq]
  simp only [map_mul, translate_C, map_finsuppProd, map_pow, translate_X]
  congr 1
  exact Finsupp.prod_fintype a (fun i n => ((X i : MvPolynomial (Fin d) ℂ) + 1) ^ n) (by simp)

/-- The multivariate binomial coefficient factors coordinate by coordinate. -/
theorem coeff_product_shifted_powers (a b : Fin d → ℕ) :
    coeff (exponent b) (∏ i : Fin d, ((X i : MvPolynomial (Fin d) ℂ) + 1) ^ a i) =
      ∏ i : Fin d, (Nat.choose (a i) (b i) : ℂ) := by
  induction d with
  | zero =>
    have he : exponent b = 0 := Subsingleton.elim _ _
    simp [he]
  | succ n ih =>
    let m : Fin n →₀ ℕ := exponent (fun i => b i.succ)
    have he : exponent b = m.cons (b 0) := by
      ext i
      refine Fin.cases ?_ (fun j => ?_) i <;> simp [m]
    rw [he, ← finSuccEquiv_coeff_coeff]
    have hp : finSuccEquiv ℂ n
        (∏ i : Fin (n + 1), ((X i : MvPolynomial (Fin (n + 1)) ℂ) + 1) ^ a i) =
        (Polynomial.X + 1) ^ a 0 * Polynomial.C
          (∏ i : Fin n, ((X i : MvPolynomial (Fin n) ℂ) + 1) ^ a i.succ) := by
      rw [Fin.prod_univ_succ, map_mul]
      simp only [map_prod, map_pow, map_add, map_one,
        finSuccEquiv_X_zero, finSuccEquiv_X_succ]
    rw [hp, Polynomial.coeff_mul_C, Polynomial.coeff_X_add_one_pow]
    have hcast : (Nat.choose (a 0) (b 0) : MvPolynomial (Fin n) ℂ) = C (Nat.choose (a 0) (b 0) : ℂ) := by simp
    rw [hcast, coeff_C_mul, ih, Fin.prod_univ_succ]

theorem coeff_translate_monomial (a b : Fin d →₀ ℕ) (c : ℂ) :
    coeff b (translate (monomial a c)) = c * ∏ i : Fin d, (Nat.choose (a i) (b i) : ℂ) := by
  rw [translate_monomial, coeff_C_mul]
  have hb : exponent (fun i => b i) = b := by ext i; simp
  rw [← hb]
  exact congrArg (fun x => c * x) (coeff_product_shifted_powers (fun i => a i) (fun i => b i))

/-- Translation of an alternant extracts an actual binomial determinant. -/
theorem coeff_translate_alternant (a b : Fin d → ℕ) :
    coeff (exponent b) (translate (alternant a)) =
      Matrix.det (fun i j : Fin d => (Nat.choose (a j) (b i) : ℂ)) := by
  classical
  simp only [alternant, Matrix.det_apply, map_sum]
  rw [MvPolynomial.coeff_sum]
  simp only [Units.smul_def, map_zsmul, coeff_smul]
  apply Finset.sum_congr rfl
  intro s _
  rw [permuted_power_product]
  simp only [coeff_translate_monomial, one_mul, exponent_apply]
  congr 1
  simpa using (Equiv.prod_comp s (fun i => (Nat.choose (a (s.symm i)) (b i) : ℂ))).symm

end FreeEntropy.WeylCharacter
