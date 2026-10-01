/-
Copyright (c) 2026 Free Entropy formalization contributors.
See LICENSE and NOTICE in the repository root for license and attribution.
-/

import FreeEntropy.SchurProbability
import Mathlib.Algebra.BigOperators.Module

/-!
# The positive-root GT formula is the actual weight character

Summation by parts identifies each positive-root expression with the
monomial of the pattern's actual successive-row-sum weight. Thus the
combinatorial probability bound concerns a genuine GT character sum.
-/
noncomputable section
open scoped BigOperators
namespace FreeEntropy.SchurProbability
open WordTypes GelfandTsetlin KostantWeightData KostantCounting
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
attribute [local instance] Classical.propDecidable
local instance {r : ℕ} {mu : Fin r → ℤ} : DecidableEq (Pattern mu) := Classical.decEq _

/-- Discrete integration by parts for the simple-root cut coefficients. -/
theorem cut_pairing (r : ℕ) (c L : ℕ → ℝ) (hzero : c 0 = 0) (hend : c r = 0) :
    (∑ i ∈ Finset.range r, (c (i + 1) - c i) * L i) =
      -(∑ j ∈ Finset.range (r - 1), c (j + 1) * (L (j + 1) - L j)) := by
  have h := Finset.sum_range_by_parts L (fun i => c (i + 1) - c i) r
  simp only [smul_eq_mul, Finset.sum_range_sub, hzero, hend, sub_zero, mul_zero, zero_sub] at h
  simpa only [mul_comm] using h

theorem adjacent_pos {r : ℕ} (x : Fin r → ℝ) (hx : ∀ i, 0 < x i)
    (j : ℕ) (hj : j + 1 < r) : 0 < adjacent x j := by
  rw [adjacent, dif_pos hj]
  exact div_pos (hx _) (hx _)

/-- Each root-form summand is the genuine monomial of the GT weight. -/
theorem gt_monomial_eq {r : ℕ} (lam : Fin r → ℕ) (x : Fin r → ℝ) (hx : ∀ i, 0 < x i)
    (P : Pattern (integralRow lam)) :
    (∏ i, x i ^ weight P i) = monomial lam x * rootWeight r (adjacent x) (drops P) := by
  let c : ℕ → ℝ := fun j => typeAOffset r (drops P) j
  let L : ℕ → ℝ := fun j => if hj : j < r then Real.log (x ⟨j, hj⟩) else 0
  have hc0 : c 0 = 0 := by simp [c]
  have hcr : c r = 0 := by simp [c, typeAOffset_eq_zero_of_le r (drops P) r le_rfl]
  have hcut := cut_pairing r c L hc0 hcr
  have hfin : (∑ i : Fin r, (c (i.val + 1) - c i.val) * Real.log (x i)) =
      ∑ i ∈ Finset.range r, (c (i + 1) - c i) * L i := by
    calc
      _ = ∑ i : Fin r, (c (i.val + 1) - c i.val) * L i.val := by
        apply Finset.sum_congr rfl
        intro i _
        simp [L, i.isLt]
      _ = _ := Fin.sum_univ_eq_sum_range (fun i => (c (i + 1) - c i) * L i) r
  have hrootpos : 0 < rootWeight r (adjacent x) (drops P) := by
    apply Finset.prod_pos
    intro j hj
    exact pow_pos (adjacent_pos x hx j (by have h := Finset.mem_range.mp hj; omega)) _
  have hrootlog : Real.log (rootWeight r (adjacent x) (drops P)) =
      ∑ j ∈ Finset.range (r - 1), c (j + 1) * (L (j + 1) - L j) := by
    unfold rootWeight
    rw [Real.log_prod (fun j hj => pow_ne_zero _
      (adjacent_pos x hx j (by have h := Finset.mem_range.mp hj; omega)).ne')]
    apply Finset.sum_congr rfl
    intro j hj
    have h1 : j + 1 < r := by have h := Finset.mem_range.mp hj; omega
    have h0 : j < r := by omega
    rw [Real.log_pow, adjacent, dif_pos h1, Real.log_div (hx _).ne' (hx _).ne']
    simp only [c, L, dif_pos h1, dif_pos h0]
  have htoplog : Real.log (monomial lam x) = ∑ i, (lam i : ℝ) * Real.log (x i) := by
    rw [monomial, Real.log_prod (fun i _ => pow_ne_zero _ (hx i).ne')]
    simp only [Real.log_pow]
  have hw : (∑ i, (weight P i : ℝ) * Real.log (x i)) =
      Real.log (monomial lam x) + Real.log (rootWeight r (adjacent x) (drops P)) := by
    rw [htoplog, hrootlog]
    simp only [weight_eq_top_sub_offset P, Pi.sub_apply, Int.cast_sub, coordinateOffset,
      Int.cast_natCast, integralRow, sub_mul, Finset.sum_sub_distrib]
    have hc' : (∑ i : Fin r, c (i.val + 1) * Real.log (x i)) -
        (∑ i : Fin r, c i.val * Real.log (x i)) =
        -(∑ j ∈ Finset.range (r - 1), c (j + 1) * (L (j + 1) - L j)) := by
      rw [← Finset.sum_sub_distrib]
      simp only [← sub_mul]
      exact hfin.trans hcut
    change (∑ i : Fin r, (lam i : ℝ) * Real.log (x i)) -
      ((∑ i : Fin r, c (i.val + 1) * Real.log (x i)) -
        ∑ i : Fin r, c i.val * Real.log (x i)) = _
    rw [hc']
    ring
  have htpos : 0 < monomial lam x := Finset.prod_pos (fun i _ => pow_pos (hx i) _)
  have hwpos : 0 < ∏ i, x i ^ weight P i := Finset.prod_pos (fun i _ => zpow_pos (hx i) _)
  calc
    (∏ i, x i ^ weight P i) = Real.exp (Real.log (∏ i, x i ^ weight P i)) :=
      (Real.exp_log hwpos).symm
    _ = Real.exp (∑ i, (weight P i : ℝ) * Real.log (x i)) := by
      rw [Real.log_prod (fun i _ => zpow_ne_zero _ (hx i).ne')]
      simp only [Real.log_zpow]
    _ = _ := by rw [hw, Real.exp_add, Real.exp_log htpos, Real.exp_log hrootpos]

/-- The character used in the pointwise estimate is precisely the finite
sum of the monomials of the actual GT weights. -/
theorem gtCharacter_eq_weight_sum {r : ℕ} (lam : Fin r → ℕ) (x : Fin r → ℝ)
    (hx : ∀ i, 0 < x i) :
    gtCharacter lam x = ∑ P : Pattern (integralRow lam), ∏ i, x i ^ weight P i := by
  apply Finset.sum_congr rfl
  intro P _
  exact (gt_monomial_eq lam x hx P).symm

/-- Pointwise Schur–Weyl estimate for the actual standard-tableau count
and the actual GT-weight character sum, with no probability-bound premise. -/
theorem tableau_gt_character_le {r n : ℕ} (lam : Fin r → ℕ)
    (hn : 0 < n) (hsize : ∑ i, lam i = n)
    (x : Fin r → ℝ) (hx : ∀ i, 0 < x i) (hanti : Antitone x) :
    (Fintype.card (SchurProbabilityTableaux.StandardTableau lam n) : ℝ) *
      (∑ P : Pattern (integralRow lam), ∏ i, x i ^ weight P i) ≤
        ((n : ℝ) + 1) ^ (r.choose 2) *
          Real.exp (-(n : ℝ) * FiniteConcentration.kl (empirical lam n) x) := by
  rw [← gtCharacter_eq_weight_sum lam x hx]
  exact schurMass_le lam hn hsize x hx hanti

/-- Nonnegative top rows give nonnegative actual GT weights, so the
character above is a polynomial monomial sum rather than a Laurent sum. -/
theorem gt_weight_nonneg {r : ℕ} (lam : Fin r → ℕ)
    (P : Pattern (integralRow lam)) (i : Fin r) : 0 ≤ weight P i := by
  have htop (j : Fin r) : (0 : ℤ) ≤ integralRow lam j ∧
      integralRow lam j ≤ (∑ k, lam k : ℕ) := by
    change (0 : ℤ) ≤ (lam j : ℤ) ∧ (lam j : ℤ) ≤ (∑ k, lam k : ℕ)
    constructor
    · exact_mod_cast Nat.zero_le (lam j)
    · exact_mod_cast Finset.single_le_sum (f := lam) (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
  have hlast := (entry_bounds P htop i.succ (Fin.last i.val)).1
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun j _ => P.upper i j)
  unfold weight rowSum
  change 0 ≤ (∑ j : Fin (i.val + 1), P.entry i.succ j) -
    (∑ j : Fin i.val, P.entry i.castSucc j)
  rw [Fin.sum_univ_castSucc (fun j => P.entry i.succ j)]
  omega

/-- The standard polynomial form of the GT Schur character. -/
theorem gtCharacter_eq_nat_weight_sum {r : ℕ} (lam : Fin r → ℕ) (x : Fin r → ℝ)
    (hx : ∀ i, 0 < x i) :
    gtCharacter lam x = ∑ P : Pattern (integralRow lam), ∏ i, x i ^ (weight P i).toNat := by
  rw [gtCharacter_eq_weight_sum lam x hx]
  apply Finset.sum_congr rfl
  intro P _
  apply Finset.prod_congr rfl
  intro i _
  conv_lhs => rw [← Int.toNat_of_nonneg (gt_weight_nonneg lam P i)]
  rw [zpow_natCast]

end FreeEntropy.SchurProbability
