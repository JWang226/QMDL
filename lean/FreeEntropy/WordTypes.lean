/-
Copyright (c) 2026 Free Entropy formalization contributors.
See LICENSE and NOTICE in the repository root for license and attribution.
-/

import FreeEntropy.FiniteConcentration
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Order.WellFounded

/-!
# Word types and the classical entropy bound

The type-class multiplicity is the actual finite count of words of fixed
content. Its probability bound follows by inclusion in all words and the
finite product-of-sums identity, not from an assumed entropy estimate.
-/
noncomputable section
open scoped BigOperators
namespace FreeEntropy.WordTypes
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
attribute [local instance] Classical.propDecidable

variable {r n : ℕ}

def content (w : Fin n → Fin r) (i : Fin r) : ℕ :=
  (Finset.univ.filter (fun t => w t = i)).card

def Words (lam : Fin r → ℕ) := {w : Fin n → Fin r // content w = lam}

instance (lam : Fin r → ℕ) : Fintype (Words (n := n) lam) := inferInstanceAs (Fintype {w // content w = lam})

def monomial (lam : Fin r → ℕ) (x : Fin r → ℝ) : ℝ := ∏ i, x i ^ lam i

def empirical (lam : Fin r → ℕ) (n : ℕ) (i : Fin r) : ℝ := (lam i : ℝ) / n

theorem word_probability_eq (w : Fin n → Fin r) (x : Fin r → ℝ) :
    (∏ t, x (w t)) = monomial (content w) x := by
  simpa only [monomial, content, Finset.prod_const] using
    (Finset.prod_fiberwise' Finset.univ w x).symm

/-- The total probability of all length-n words is exactly one. -/
theorem all_word_probability (x : Fin r → ℝ) (hx : ∑ i, x i = 1) :
    (∑ w : Fin n → Fin r, ∏ t, x (w t)) = 1 := by
  rw [← Fintype.prod_sum (fun (_t : Fin n) (i : Fin r) => x i)]
  simp only [hx, Finset.prod_const_one]

/-- Every type class is a subset of all words. -/
theorem type_probability_le_one (lam : Fin r → ℕ) (x : Fin r → ℝ)
    (hx : ∀ i, 0 ≤ x i) (hx1 : ∑ i, x i = 1) :
    (Fintype.card (Words (n := n) lam) : ℝ) * monomial lam x ≤ 1 := by
  have hs : (∑ w ∈ Finset.univ.filter (fun w : Fin n → Fin r => content w = lam),
      ∏ t, x (w t)) ≤ ∑ w : Fin n → Fin r, ∏ t, x (w t) :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      (fun _ _ _ => Finset.prod_nonneg (fun i _ => hx _))
  rw [all_word_probability x hx1] at hs
  have heq : (∑ w ∈ Finset.univ.filter (fun w : Fin n → Fin r => content w = lam),
      ∏ t, x (w t)) = (Fintype.card (Words (n := n) lam) : ℝ) * monomial lam x := by
    calc
      _ = ∑ _w ∈ Finset.univ.filter (fun w : Fin n → Fin r => content w = lam), monomial lam x := by
        apply Finset.sum_congr rfl
        intro w hw
        rw [word_probability_eq, (Finset.mem_filter.mp hw).2]
      _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul, Words, Fintype.card_subtype]
  rwa [heq] at hs

theorem empirical_sum (lam : Fin r → ℕ) (hn : 0 < n) (hlam : ∑ i, lam i = n) :
    ∑ i, empirical lam n i = 1 := by
  simp only [empirical, ← Finset.sum_div, ← Nat.cast_sum, hlam]
  exact div_self (by exact_mod_cast hn.ne')

theorem empirical_monomial_pos (lam : Fin r → ℕ) (hn : 0 < n) :
    0 < monomial lam (empirical lam n) := by
  apply Finset.prod_pos
  intro i _
  by_cases hi : lam i = 0
  · simp [hi]
  · apply pow_pos
    exact div_pos (by exact_mod_cast Nat.pos_of_ne_zero hi) (by exact_mod_cast hn)

/-- Exact exponential identity, including empty coordinates of the type. -/
theorem entropy_exponential (lam : Fin r → ℕ) (hn : 0 < n) (x : Fin r → ℝ)
    (hx : ∀ i, 0 < x i) :
    Real.exp (-(n : ℝ) * FiniteConcentration.kl (empirical lam n) x) =
      monomial lam x / monomial lam (empirical lam n) := by
  unfold FiniteConcentration.kl monomial
  rw [Finset.mul_sum, Real.exp_sum, ← Finset.prod_div_distrib]
  apply Finset.prod_congr rfl
  intro i _
  by_cases hi : lam i = 0
  · simp [empirical, hi]
  · have hp : 0 < empirical lam n i :=
      div_pos (by exact_mod_cast Nat.pos_of_ne_zero hi) (by exact_mod_cast hn)
    have hm : -(n : ℝ) * (empirical lam n i * Real.log (empirical lam n i / x i)) =
        (lam i : ℝ) * (Real.log (x i) - Real.log (empirical lam n i)) := by
      rw [Real.log_div hp.ne' (hx i).ne']
      unfold empirical
      field_simp
      ring
    rw [hm, Real.exp_nat_mul, Real.exp_sub, Real.exp_log (hx i), Real.exp_log hp, div_pow]

/-- Actual type-class counts obey the usual method-of-types entropy bound. -/
theorem type_probability_le_exp_neg_kl (lam : Fin r → ℕ) (hn : 0 < n)
    (hlam : ∑ i, lam i = n) (x : Fin r → ℝ) (hx : ∀ i, 0 < x i) :
    (Fintype.card (Words (n := n) lam) : ℝ) * monomial lam x ≤
      Real.exp (-(n : ℝ) * FiniteConcentration.kl (empirical lam n) x) := by
  have he := type_probability_le_one (n := n) lam (empirical lam n)
    (fun i => div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) (empirical_sum lam hn hlam)
  rw [entropy_exponential lam hn x hx]
  apply (le_div_iff₀ (empirical_monomial_pos lam hn)).mpr
  have hm := mul_le_mul_of_nonneg_right he
    (show 0 ≤ monomial lam x from Finset.prod_nonneg (fun i _ => pow_nonneg (hx i).le _))
  nlinarith

end FreeEntropy.WordTypes
