/-
Copyright (c) 2026 Free Entropy formalization contributors.
See LICENSE and NOTICE in the repository root for license and attribution.
-/

import FreeEntropy.SchurWeylConcentrationMonomial
import FreeEntropy.SchurWeylConcentrationSupport
import FreeEntropy.TensorSectorDimension

/-! An actual physical tensor-state probability estimate. The source blocks,
copy count, highest monomial, and polynomial dimension bound are all derived.
No representation probability estimate is assumed. -/
noncomputable section
open Matrix
open scoped BigOperators
namespace FreeEntropy.SchurWeyl
open Occupation WordTypes
set_option backward.isDefEq.respectTransparency false
variable {d n : ℕ}

/-- Sum of the actual tensor-state block probabilities sharing a highest row. -/
def highestSectorMass (lam : Occupation d n) (x : Fin d → ℝ) : ℝ :=
  ∑ i : SectorsAt lam, sectorProbability n (Matrix.diagonal (fun j => (x j : ℂ))) i.val

def concentrationExponent (d : ℕ) : ℕ := (d - 1) * (d.choose 2)

theorem highestSectorMass_le_type (lam : Occupation d n) (x : Fin d → ℝ)
    (hx : ∀ j, 0 ≤ x j) (hanti : Antitone x) :
    highestSectorMass lam x ≤ ((n : ℝ) + 1) ^ concentrationExponent d *
      ((Fintype.card (Words (n := n) lam.val) : ℝ) * monomial lam.val x) := by
  have hm : 0 ≤ monomial lam.val x := Finset.prod_nonneg (fun i _ => pow_nonneg (hx i) _)
  have hdim (i : SectorsAt lam) : (Fintype.card (SectorSpace d n i.val) : ℝ) ≤
      ((n : ℝ) + 1) ^ concentrationExponent d := by
    exact_mod_cast sector_card_le_polynomial i.val
  have hc : (Fintype.card (SectorsAt lam) : ℝ) ≤
      (Fintype.card (Words (n := n) lam.val) : ℝ) := by
    exact_mod_cast sectorsAt_card_le_words lam
  calc
    highestSectorMass lam x ≤ ∑ i : SectorsAt lam,
        ((n : ℝ) + 1) ^ concentrationExponent d * monomial lam.val x := by
      apply Finset.sum_le_sum
      intro i _
      have h := sectorProbability_le_highest i.val x hx hanti
      rw [i.property] at h
      exact h.trans (mul_le_mul_of_nonneg_right (hdim i) hm)
    _ = (Fintype.card (SectorsAt lam) : ℝ) *
        (((n : ℝ) + 1) ^ concentrationExponent d * monomial lam.val x) := by simp
    _ ≤ (Fintype.card (Words (n := n) lam.val) : ℝ) *
        (((n : ℝ) + 1) ^ concentrationExponent d * monomial lam.val x) :=
      mul_le_mul_of_nonneg_right hc (mul_nonneg (by positivity) hm)
    _ = _ := by ring

/-- The actual grouped Schur probabilities obey a method-of-types bound.
The polynomial is deliberately coarse; it has the same squared-log decay. -/
theorem highestSectorMass_le_exp_neg_kl (lam : Occupation d n) (hn : 0 < n)
    (x : Fin d → ℝ) (hx : ∀ j, 0 ≤ x j) (hanti : Antitone x)
    (hsupp : ∀ j, lam.val j ≠ 0 → 0 < x j) :
    highestSectorMass lam x ≤ ((n : ℝ) + 1) ^ concentrationExponent d *
      Real.exp (-(n : ℝ) * FiniteConcentration.kl (empirical lam.val n) x) :=
  (highestSectorMass_le_type lam x hx hanti).trans
    (mul_le_mul_of_nonneg_left (type_probability_le_exp_neg_kl_of_support lam.val hn
      lam.property x hx hsupp) (by positivity))

/-- If an occupation uses a zero eigenvalue, its entire actual grouped
probability vanishes from above, so no undefined relative entropy is used. -/
theorem highestSectorMass_le_zero_of_unsupported (lam : Occupation d n)
    (x : Fin d → ℝ) (hx : ∀ j, 0 ≤ x j) (hanti : Antitone x)
    (j : Fin d) (hxj : x j = 0) (hlam : lam.val j ≠ 0) :
    highestSectorMass lam x ≤ 0 := by
  have hm : monomial lam.val x = 0 := by
    exact Finset.prod_eq_zero (Finset.mem_univ j) (by simp [hxj, hlam])
  have h := highestSectorMass_le_type lam x hx hanti
  simpa only [hm, mul_zero] using h

end FreeEntropy.SchurWeyl
