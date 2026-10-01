/-
Copyright (c) 2026 Free Entropy formalization contributors.
See LICENSE and NOTICE in the repository root for license and attribution.
-/

import FreeEntropy.WeylCombinatorics
import FreeEntropy.Cloning
import Mathlib.Data.Nat.Choose.Cast

/-!
# The finite Weyl dimension-ratio bound from actual rows

The product here is the Weyl product, with all pairs of rows included.
Its ratio estimate is derived from row order, supported adjacent gaps,
and the L1 size of the dominant difference. Identifying this product with
an irreducible representation dimension remains a representation theorem.
-/

noncomputable section
open scoped BigOperators
namespace FreeEntropy.Weyl

def rowL1 (d : ℕ) (ω : ℕ → ℝ) : ℝ := ∑ i ∈ Finset.range d, |ω i|

theorem row_difference_le_l1 (d i j : ℕ) (ω : ℕ → ℝ)
    (hi : i < d) (hj : j < d) (hij : i ≠ j) :
    ω i - ω j ≤ rowL1 d ω := by
  have hs : ({i, j} : Finset ℕ) ⊆ Finset.range d := by
    intro k hk
    simp only [Finset.mem_insert, Finset.mem_singleton] at hk
    rcases hk with rfl | rfl <;> exact Finset.mem_range.mpr (by assumption)
  have h := Finset.sum_le_sum_of_subset_of_nonneg hs (fun k _ _ => abs_nonneg (ω k))
  have he : (∑ k ∈ ({i, j} : Finset ℕ), |ω k|) = |ω i| + |ω j| := by simp [hij]
  rw [he] at h
  exact (by linarith [le_abs_self (ω i), neg_le_abs (ω j)] :
    ω i - ω j ≤ |ω i| + |ω j|).trans h

theorem all_root_count (d : ℕ) : ((activeRoots d d).card : ℝ) = (d.choose 2 : ℝ) := by
  rw [card_activeRoots_real d d le_rfl, Nat.cast_choose_two]
  ring

def rootDenominator (μ : ℕ → ℝ) (p : ℕ × ℕ) : ℝ :=
  μ p.1 - μ p.2 + (p.2 - p.1 : ℕ)

theorem weyl_product_ratio (d : ℕ) (μ ω : ℕ → ℝ) :
    activeProduct d d μ / activeProduct d d (fun i => μ i + ω i) =
      ∏ p ∈ activeRoots d d,
        rootDenominator μ p / (rootDenominator μ p + (ω p.1 - ω p.2)) := by
  unfold activeProduct
  rw [← Finset.prod_div_distrib]
  apply Finset.prod_congr rfl
  intro p hp
  have hg : ((p.2 - p.1 : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.sub_pos_of_lt (mem_activeRoots.mp hp).2.1).ne'
  unfold rootDenominator
  rw [div_div_div_cancel_right₀ hg]
  congr 1
  ring

/-- Lemma `dim_ratio` with the Weyl formula substituted explicitly. No
dimension-loss inequality is assumed: it follows from the row hypotheses.
The zero increment below rank `r` avoids imposing a gap on padded zero rows. -/
theorem weyl_ratio_deficit_from_rows (d r : ℕ) (μ ω : ℕ → ℝ) (b : ℝ)
    (hb : 0 ≤ b)
    (hμ : ∀ i j, i < j → j < d → μ j ≤ μ i)
    (hω : ∀ i j, i < j → j < d → ω j ≤ ω i)
    (hzero : ∀ i, r ≤ i → i < d → ω i = 0)
    (hgap : ∀ i, i < r → i + 1 < d → b ≤ μ i - μ (i + 1)) :
    1 - activeProduct d d μ / activeProduct d d (fun i => μ i + ω i) ≤
      (d.choose 2 : ℝ) * rowL1 d ω / (b + 1) := by
  rw [weyl_product_ratio]
  have h := Cloning.weyl_product_deficit_le_card (activeRoots d d)
    (rootDenominator μ) (fun p => ω p.1 - ω p.2) b (rowL1 d ω) hb
  rw [all_root_count] at h
  apply h
  · intro p hp
    obtain ⟨hi, hij, hj⟩ := mem_activeRoots.mp hp
    have hpos : (0 : ℝ) < (p.2 - p.1 : ℕ) := by exact_mod_cast Nat.sub_pos_of_lt hij
    have hord := hμ p.1 p.2 hij hj
    dsimp [rootDenominator]
    linarith
  · intro p hp
    obtain ⟨hi, hij, hj⟩ := mem_activeRoots.mp hp
    by_cases hir : p.1 < r
    · right
      have hig : p.1 + 1 < d := lt_of_le_of_lt (Nat.succ_le_of_lt hij) hj
      have hg := hgap p.1 hir hig
      have hmono : μ p.2 ≤ μ (p.1 + 1) := by
        rcases (Nat.succ_le_of_lt hij).eq_or_lt with he | he
        · have he' : p.1 + 1 = p.2 := by omega
          rw [he']
        · exact hμ _ _ he hj
      have hdist : (1 : ℝ) ≤ (p.2 - p.1 : ℕ) := by
        exact_mod_cast (Nat.one_le_iff_ne_zero.mpr (Nat.sub_pos_of_lt hij).ne')
      dsimp [rootDenominator]
      linarith
    · left
      dsimp only
      rw [hzero p.1 (Nat.le_of_not_gt hir) hi,
        hzero p.2 (by omega) hj, sub_self]
  · intro p hp
    exact sub_nonneg.mpr (hω p.1 p.2 (mem_activeRoots.mp hp).2.1 (mem_activeRoots.mp hp).2.2)
  · intro p hp
    obtain ⟨hi, hij, hj⟩ := mem_activeRoots.mp hp
    exact row_difference_le_l1 d p.1 p.2 ω hi hj hij.ne

end FreeEntropy.Weyl
