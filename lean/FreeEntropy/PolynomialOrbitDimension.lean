/-
Copyright (c) 2026 Free Entropy formalization contributors.
See LICENSE and NOTICE in the repository root for license and attribution.
-/

import Mathlib.Data.Complex.Basic
import Mathlib.Algebra.CharZero.Infinite
import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Dimension.Finrank

/-! Distinct polynomial orbit coordinates force actual dimension lower bounds.
This is the linear-algebra bridge from explicit exterior minors to independent
weight directions; it assumes no representation dimension formula. -/
noncomputable section
open scoped BigOperators
namespace FreeEntropy.PolynomialOrbit
set_option backward.isDefEq.respectTransparency false

variable {I V E : Type*} [Fintype I] [AddCommGroup E] [Module ℂ E]

/-- Linear functionals that restrict to distinct monomials on one orbit are
linearly independent, by polynomial uniqueness over the infinite field ℂ. -/
theorem monomial_functionals_independent (f : I → Module.Dual ℂ E)
    (orbit : (V → ℂ) → E) (exponent : I → V →₀ ℕ)
    (hinj : Function.Injective exponent)
    (hmon : ∀ i x, f i (orbit x) =
      MvPolynomial.eval x (MvPolynomial.monomial (exponent i) (1 : ℂ))) :
    LinearIndependent ℂ f := by
  classical
  apply Fintype.linearIndependent_iff.mpr
  intro c hc i
  let p : MvPolynomial V ℂ := ∑ j, MvPolynomial.monomial (exponent j) (c j)
  have hp : p = 0 := by
    apply MvPolynomial.funext
    intro x
    have h := congrArg (fun l : Module.Dual ℂ E => l (orbit x)) hc
    simp only [LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.zero_apply,
      smul_eq_mul, hmon] at h
    simpa [p, MvPolynomial.eval_monomial, mul_comm] using h
  have hi := congrArg (MvPolynomial.coeff (exponent i)) hp
  simpa [p, MvPolynomial.coeff_sum, MvPolynomial.coeff_monomial, hinj.eq_iff] using hi

/-- The number of distinct monomial orbit coordinates bounds the true
dimension of the space containing that orbit. -/
theorem card_le_finrank_of_monomial_orbit [FiniteDimensional ℂ E]
    (f : I → Module.Dual ℂ E) (orbit : (V → ℂ) → E) (exponent : I → V →₀ ℕ)
    (hinj : Function.Injective exponent)
    (hmon : ∀ i x, f i (orbit x) =
      MvPolynomial.eval x (MvPolynomial.monomial (exponent i) (1 : ℂ))) :
    Fintype.card I ≤ Module.finrank ℂ E := by
  have h := (monomial_functionals_independent f orbit exponent hinj hmon).fintype_card_le_finrank
  simpa only [Subspace.dual_finrank_eq] using h

end FreeEntropy.PolynomialOrbit
