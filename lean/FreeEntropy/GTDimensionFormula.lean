/-
Copyright (c) 2026 Free Entropy formalization contributors.
See LICENSE and NOTICE in the repository root for license and attribution.
-/

import FreeEntropy.GTCardinality
import FreeEntropy.GTWeylProduct
import FreeEntropy.TypicalRows
import FreeEntropy.GTPartitions

/-!
# The Weyl dimension formula for the actual GT basis

The finite cardinality is proved by branching and a binomial determinant,
then identified with the full root product. Trailing zero rows reduce it to
the supported product. The manuscript's padded target therefore has the
claimed dimension and exact logarithmic expansion without a dimension premise.
-/

noncomputable section
open Filter
open scoped BigOperators Topology

namespace FreeEntropy.GTDimension
open GelfandTsetlin

theorem binomialDet_eq_activeProduct (n : ℕ) (μ : ℕ → ℤ) :
    binomialDet (fun i : Fin n => μ i.val) =
      Weyl.activeProduct n n (fun i => (μ i : ℝ)) := by
  rw [binomialDet, chooseDet_product]
  simp only [shiftedRow, Int.cast_add, Int.cast_natCast]
  rw [reversed_shifted_numerator, ← full_denominator]
  unfold Weyl.activeProduct
  rw [Finset.prod_div_distrib]

/-- The actual finite type of integral GT patterns has the full Weyl dimension. -/
theorem card_eq_fullWeyl (n : ℕ) (μ : ℕ → ℤ)
    (hμ : Dominant (fun i : Fin n => μ i.val)) :
    (Fintype.card (Pattern (fun i : Fin n => μ i.val)) : ℝ) =
      Weyl.activeProduct n n (fun i => (μ i : ℝ)) := by
  rw [card_eq_binomialDet _ hμ, binomialDet_eq_activeProduct]

/-- The active-root formula follows from the actual cardinality when the
top row vanishes below the supported rank. -/
theorem card_eq_activeWeyl (d r : ℕ) (hr : r ≤ d) (μ : ℕ → ℤ)
    (hμ : Dominant (fun i : Fin d => μ i.val))
    (hzero : ∀ i, r ≤ i → i < d → μ i = 0) :
    (Fintype.card (Pattern (fun i : Fin d => μ i.val)) : ℝ) =
      Weyl.activeProduct d r (fun i => (μ i : ℝ)) := by
  rw [card_eq_fullWeyl d μ hμ]
  apply full_product_eq_active d r hr
  intro i hir hid
  simp [hzero i hir hid]

/-- Integer coordinates of the prescribed padded target. -/
def targetIntegerRow {d r : ℕ} (s : FixedSpectrum d r) (n i : ℕ) : ℤ :=
  if i < r then paddedRow n (s.eigenvalue i) (typicalWidth n) (r - i : ℕ) else 0

@[simp] theorem targetIntegerRow_cast {d r : ℕ} (s : FixedSpectrum d r) (n i : ℕ) :
    (targetIntegerRow s n i : ℝ) = s.targetRow n i := by
  simp only [targetIntegerRow, FixedSpectrum.targetRow]
  split <;> simp

theorem width_nonneg_all (n : ℕ) : 0 ≤ typicalWidth n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [typicalWidth]
  · exact TypicalRows.width_nonneg n hn

theorem targetIntegerRow_nonneg {d r : ℕ} (s : FixedSpectrum d r) (n i : ℕ) :
    0 ≤ targetIntegerRow s n i := by
  unfold targetIntegerRow
  split_ifs with hi
  · apply Int.ceil_nonneg
    exact add_nonneg (mul_nonneg (Nat.cast_nonneg n) (s.positive i hi).le)
      (mul_nonneg (Nat.cast_nonneg _) (by linarith [width_nonneg_all n]))
  · exact le_rfl

theorem targetIntegerRow_dominant {d r : ℕ} (s : FixedSpectrum d r) (n : ℕ) :
    Dominant (fun i : Fin d => targetIntegerRow s n i.val) := by
  intro i j hij
  by_cases hj : j.val < r
  · have hi : i.val < r := lt_of_le_of_lt hij hj
    have he : s.eigenvalue j.val ≤ s.eigenvalue i.val := by
      rcases lt_or_eq_of_le hij with hlt | heq
      · exact (s.decreasing i.val j.val hlt hj).le
      · rw [heq]
    have hk : ((r - j.val : ℕ) : ℝ) ≤ (r - i.val : ℕ) := by
      exact_mod_cast Nat.sub_le_sub_left hij r
    simp only [targetIntegerRow, hi, hj, ↓reduceIte, paddedRow]
    apply Int.ceil_mono
    exact add_le_add (mul_le_mul_of_nonneg_left he (Nat.cast_nonneg n))
      (mul_le_mul_of_nonneg_right hk (by linarith [width_nonneg_all n]))
  · simpa only [targetIntegerRow, hj, ↓reduceIte] using targetIntegerRow_nonneg s n i.val

/-- The memory dimension of the actual GT basis of the padded target. -/
def targetDimension {d r : ℕ} (s : FixedSpectrum d r) (n : ℕ) : ℕ :=
  Fintype.card (Pattern (fun i : Fin d => targetIntegerRow s n i.val))

theorem targetDimension_pos {d r : ℕ} (s : FixedSpectrum d r) (n : ℕ) :
    0 < targetDimension s n := by
  haveI : Nonempty (Pattern (fun i : Fin d => targetIntegerRow s n i.val)) :=
    ⟨GelfandTsetlin.highestPattern _ (targetIntegerRow_dominant s n)⟩
  exact Fintype.card_pos

theorem targetDimension_weyl {d r : ℕ} (s : FixedSpectrum d r) (n : ℕ) :
    (targetDimension s n : ℝ) = Weyl.activeProduct d r (s.targetRow n) := by
  have h := card_eq_activeWeyl d r s.rank_le (targetIntegerRow s n)
    (targetIntegerRow_dominant s n) (fun i hi _ => by
      simp [targetIntegerRow, Nat.not_lt.mpr hi])
  simpa only [targetDimension, targetIntegerRow_cast] using h

/-- Exact memory expansion for the actual finite GT basis of the padded target. -/
theorem targetDimension_log_asymptotic {d r : ℕ} (s : FixedSpectrum d r) :
    Tendsto (fun n => Real.logb 2 (targetDimension s n) -
      Weyl.qmdl d r s.eigenvalue n) atTop (𝓝 0) := by
  have h := Weyl.activeProduct_log_asymptotic d r s.targetRow s.eigenvalue
    s.active_gap s.targetRow_normalized_tendsto
  simpa only [← targetDimension_weyl,
    Weyl.rootLeading_eq_qmdl d r s.rank_le s.eigenvalue _ s.active_gap s.zero_padded] using h

end FreeEntropy.GTDimension
