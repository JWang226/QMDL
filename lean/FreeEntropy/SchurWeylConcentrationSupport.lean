/-
Copyright (c) 2026 Free Entropy formalization contributors.
See LICENSE and NOTICE in the repository root for license and attribution.
-/

import FreeEntropy.WordTypes

/-! The finite entropy estimates with zero eigenvalues. Reference coordinates
may vanish, provided the empirical distribution is supported there. -/
noncomputable section
open scoped BigOperators
namespace FreeEntropy.FiniteConcentration
open InformationTheory
variable {ι : Type*} [Fintype ι]

/-- The same proved quadratic entropy estimate on the support of a possibly
rank-deficient reference probability. -/
theorem l1_sq_div_four_le_kl_of_support (p q : ι → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hq : ∀ i, 0 ≤ q i)
    (hsupp : ∀ i, q i = 0 → p i = 0)
    (hp1 : ∑ i, p i = 1) (hq1 : ∑ i, q i = 1) :
    (l1 p q) ^ 2 / 4 ≤ kl p q := by
  have heach (i : ι) : q i * klFun (p i / q i) =
      p i * Real.log (p i / q i) + q i - p i := by
    by_cases hi : q i = 0
    · simp [hi, hsupp i hi]
    · unfold klFun
      field_simp [hi]
  have heq : kl p q = ∑ i, q i * klFun (p i / q i) := by
    simp_rw [heach]
    rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, hp1, hq1]
    simp [kl]
  have hh : hellingerSq p q ≤ kl p q := by
    rw [heq]
    apply Finset.sum_le_sum
    intro i _
    by_cases hi : q i = 0
    · simp [hi, hsupp i hi]
    · exact weighted_klFun_ge_sqrt (hp i) (lt_of_le_of_ne (hq i) (Ne.symm hi))
  have hl := l1_sq_le_four_hellingerSq p q hp hq hp1 hq1
  linarith

end FreeEntropy.FiniteConcentration
namespace FreeEntropy.WordTypes
variable {d n : ℕ}
set_option backward.isDefEq.respectTransparency false

theorem entropy_exponential_of_support (lam : Fin d → ℕ) (hn : 0 < n)
    (x : Fin d → ℝ) (hx : ∀ i, lam i ≠ 0 → 0 < x i) :
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
      rw [Real.log_div hp.ne' (hx i hi).ne']
      unfold empirical
      field_simp
      ring
    rw [hm, Real.exp_nat_mul, Real.exp_sub, Real.exp_log (hx i hi), Real.exp_log hp, div_pow]

theorem type_probability_le_exp_neg_kl_of_support (lam : Fin d → ℕ) (hn : 0 < n)
    (hlam : ∑ i, lam i = n) (x : Fin d → ℝ) (hx : ∀ i, 0 ≤ x i)
    (hsupp : ∀ i, lam i ≠ 0 → 0 < x i) :
    (Fintype.card (Words (n := n) lam) : ℝ) * monomial lam x ≤
      Real.exp (-(n : ℝ) * FiniteConcentration.kl (empirical lam n) x) := by
  have he := type_probability_le_one (n := n) lam (empirical lam n)
    (fun i => div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) (empirical_sum lam hn hlam)
  rw [entropy_exponential_of_support lam hn x hsupp]
  apply (le_div_iff₀ (empirical_monomial_pos lam hn)).mpr
  have hm := mul_le_mul_of_nonneg_right he
    (show 0 ≤ monomial lam x from Finset.prod_nonneg (fun i _ => pow_nonneg (hx i) _))
  nlinarith

end FreeEntropy.WordTypes
