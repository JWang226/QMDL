/-
Copyright (c) 2026 Free Entropy formalization contributors.
See LICENSE and NOTICE in the repository root for license and attribution.
-/

import FreeEntropy.WeylCharacterAlgebra
import Mathlib.LinearAlgebra.Vandermonde

/-! Alternant and Vandermonde polynomials are actual eigenpolynomials of
the flat Euler Laplacian. These are the denominator identities in the
finite-polynomial proof of the Weyl character formula. -/
noncomputable section
open scoped BigOperators
namespace FreeEntropy.WeylCharacter
open MvPolynomial
set_option backward.isDefEq.respectTransparency false
variable {d : ℕ}

def exponent (a : Fin d → ℕ) : Fin d →₀ ℕ := Finsupp.equivFunOnFinite.symm a

@[simp] theorem exponent_apply (a : Fin d → ℕ) (i : Fin d) : exponent a i = a i := by
  simp [exponent]

theorem monomial_exponent (a : Fin d → ℕ) :
    monomial (exponent a) (1 : ℂ) = ∏ i, (X i : MvPolynomial (Fin d) ℂ) ^ a i := by
  rw [MvPolynomial.monic_monomial_eq]
  simpa using Finsupp.prod_fintype (exponent a) (fun i n => (X i : MvPolynomial (Fin d) ℂ) ^ n) (by simp)

theorem laplacian_monomial (m : Fin d →₀ ℕ) (c : ℂ) :
    laplacian (monomial m c) = (exponentEnergy m : ℂ) • monomial m c := by
  classical
  ext a
  rw [coeff_laplacian, coeff_smul]
  by_cases ha : a = m
  · subst a; rfl
  · simp [coeff_monomial, ha, Ne.symm ha]

/-- The actual alternating determinant for a natural exponent row. -/
def alternant (a : Fin d → ℕ) : MvPolynomial (Fin d) ℂ :=
  Matrix.det (fun i j : Fin d => (X i : MvPolynomial (Fin d) ℂ) ^ a j)

theorem permuted_power_product (a : Fin d → ℕ) (s : Equiv.Perm (Fin d)) :
    (∏ i : Fin d, (X (s i) : MvPolynomial (Fin d) ℂ) ^ a i) =
      monomial (exponent (fun i => a (s.symm i))) 1 := by
  rw [monomial_exponent]
  simpa using Equiv.prod_comp s (fun i => (X i : MvPolynomial (Fin d) ℂ) ^ a (s.symm i))

theorem permuted_exponent_energy (a : Fin d → ℕ) (s : Equiv.Perm (Fin d)) :
    exponentEnergy (exponent (fun i => a (s.symm i))) = ∑ i, a i ^ 2 := by
  simp only [exponentEnergy, exponent_apply]
  exact s.symm.sum_comp (fun i => a i ^ 2)

theorem laplacian_sign_smul (s : Equiv.Perm (Fin d)) (p : MvPolynomial (Fin d) ℂ) :
    laplacian (Equiv.Perm.sign s • p) = Equiv.Perm.sign s • laplacian p := by
  simp only [Units.smul_def, map_zsmul]

/-- Every determinant monomial has the same squared exponent norm. -/
theorem alternant_laplacian (a : Fin d → ℕ) :
    laplacian (alternant a) = ((∑ i, a i ^ 2 : ℕ) : ℂ) • alternant a := by
  classical
  simp only [alternant, Matrix.det_apply, map_sum, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro s _
  rw [laplacian_sign_smul, permuted_power_product, laplacian_monomial,
    permuted_exponent_energy]
  exact smul_comm _ _ _

/-- The Vandermonde denominator, with factors X_j-X_i for i<j. -/
def denominator (d : ℕ) : MvPolynomial (Fin d) ℂ :=
  Matrix.det (Matrix.vandermonde (fun i : Fin d => (X i : MvPolynomial (Fin d) ℂ)))

theorem denominator_product (d : ℕ) : denominator d =
    ∏ i : Fin d, ∏ j ∈ Finset.Ioi i, ((X j : MvPolynomial (Fin d) ℂ) - X i) :=
  Matrix.det_vandermonde _

theorem denominator_laplacian (d : ℕ) :
    laplacian (denominator d) = (∑ i : Fin d, (i.val : ℂ) ^ 2) • denominator d := by
  simpa only [denominator, alternant, Matrix.vandermonde, Nat.cast_sum, Nat.cast_pow] using
    alternant_laplacian (fun i : Fin d => i.val)

end FreeEntropy.WeylCharacter
