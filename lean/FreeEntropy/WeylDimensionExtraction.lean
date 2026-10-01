/-
Copyright (c) 2026 Free Entropy formalization contributors.
See LICENSE and NOTICE in the repository root for license and attribution.
-/

import FreeEntropy.WeylTranslation
import FreeEntropy.WeylCoefficient
import FreeEntropy.GTDimensionFormula

/-! An exact polynomial character identity determines the actual dimension
by a finite binomial coefficient extraction; no analytic limit is used. -/
noncomputable section
open scoped BigOperators
namespace FreeEntropy.WeylCharacter
open MvPolynomial
set_option backward.isDefEq.respectTransparency false
variable {d : ℕ}

theorem coeff_zero_translate (p : MvPolynomial (Fin d) ℂ) :
    coeff 0 (translate p) = eval (fun _ => 1) p := by
  classical
  induction p using MvPolynomial.induction_on' with
  | monomial a c => simp [coeff_translate_monomial, eval_monomial]
  | add p q hp hq => simp only [map_add, coeff_add, hp, hq]

/-- The value at the identity of a quotient by the Weyl denominator is
an exact determinant of ordinary binomial coefficients. -/
theorem eval_one_of_alternant_identity (p : MvPolynomial (Fin d) ℂ) (a : Fin d → ℕ)
    (h : denominator d * p = alternant a) :
    eval (fun _ => 1) p = Matrix.det (fun i j : Fin d => (Nat.choose (a i) j.val : ℂ)) := by
  have ht := congrArg translate h
  simp only [map_mul, translate_denominator] at ht
  have hc := congrArg (coeff (exponent (fun i : Fin d => i.val))) ht
  rw [denominator_mul_staircase_coeff, coeff_translate_alternant, coeff_zero_translate] at hc
  exact hc.trans (Matrix.det_transpose _).symm

/-- For natural rows, the finite extraction determinant is the already
proved GT binomial determinant, over the complex coefficient field. -/
theorem extraction_eq_binomialDet (mu : Fin d → ℕ) :
    Matrix.det (fun i j : Fin d => (Nat.choose (mu i.rev + i.val) j.val : ℂ)) =
      (GTDimension.binomialDet (fun i : Fin d => (mu i : ℤ)) : ℂ) := by
  unfold GTDimension.binomialDet GTDimension.chooseDet
  change _ = Complex.ofRealHom (Matrix.det _)
  rw [Complex.ofRealHom.map_det]
  congr 1
  ext i j
  change (Nat.choose (mu i.rev + i.val) j.val : ℂ) =
    ((Ring.choose ((GTDimension.shiftedRow (fun i => (mu i : ℤ)) i : ℤ) : ℝ) j.val : ℝ) : ℂ)
  simp only [GTDimension.shiftedRow, Int.cast_add, Int.cast_natCast]
  rw [← Nat.cast_add, Ring.choose_natCast]
  rfl

/-- The exact representation dimension follows from the character identity
and its value at one; the GT cardinality formula has already been proved. -/
theorem dimension_eq_GT_of_character_identity (p : MvPolynomial (Fin d) ℂ)
    (mu : Fin d → ℕ) (hmu : Antitone mu) (dimension : ℕ)
    (heval : eval (fun _ => 1) p = (dimension : ℂ))
    (h : denominator d * p = alternant (fun i : Fin d => mu i.rev + i.val)) :
    dimension = Fintype.card (GelfandTsetlin.Pattern (fun i : Fin d => (mu i : ℤ))) := by
  have he := eval_one_of_alternant_identity p _ h
  rw [heval, extraction_eq_binomialDet] at he
  have hdom : GelfandTsetlin.Dominant (fun i : Fin d => (mu i : ℤ)) := by
    intro i j hij
    change (mu j : ℤ) ≤ (mu i : ℤ)
    exact_mod_cast hmu hij
  have hcard := GTDimension.card_eq_binomialDet (fun i : Fin d => (mu i : ℤ)) hdom
  rw [← hcard] at he
  exact_mod_cast he

end FreeEntropy.WeylCharacter
