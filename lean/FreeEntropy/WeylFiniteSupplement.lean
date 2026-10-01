/-
Copyright (c) 2026 Free Entropy formalization contributors.
See LICENSE and NOTICE in the repository root for license and attribution.
-/

import FreeEntropy.WeylFinite

/-!
# Positivity and the zero case of the finite Weyl ratio

These are statements about the actual finite Weyl products. The product is
not silently identified with an irreducible-representation dimension.
-/

noncomputable section
open scoped BigOperators

namespace FreeEntropy.Weyl

theorem rowL1_nonneg (d : ℕ) (ω : ℕ → ℝ) : 0 ≤ rowL1 d ω :=
  Finset.sum_nonneg (fun i _ => abs_nonneg (ω i))

/-- A zero L1 sum forces every supported coordinate to vanish. -/
theorem rowL1_eq_zero_iff (d : ℕ) (ω : ℕ → ℝ) :
    rowL1 d ω = 0 ↔ ∀ i, i < d → ω i = 0 := by
  constructor
  · intro h i hi
    have hle : |ω i| ≤ rowL1 d ω :=
      Finset.single_le_sum (fun j _ => abs_nonneg (ω j)) (Finset.mem_range.mpr hi)
    rw [h] at hle
    exact abs_eq_zero.mp (le_antisymm hle (abs_nonneg _))
  · intro h
    unfold rowL1
    apply Finset.sum_eq_zero
    intro i hi
    rw [h i (Finset.mem_range.mp hi), abs_zero]

/-- Ordered rows make each full Weyl numerator strictly positive, including
equal adjacent rows because the positive integer root height is added. -/
theorem rootDenominator_pos_of_ordered (d : ℕ) (μ : ℕ → ℝ)
    (hμ : ∀ i j, i < j → j < d → μ j ≤ μ i)
    (p : ℕ × ℕ) (hp : p ∈ activeRoots d d) : 0 < rootDenominator μ p := by
  obtain ⟨_, hij, hj⟩ := mem_activeRoots.mp hp
  have hgap : (0 : ℝ) < (p.2 - p.1 : ℕ) := by exact_mod_cast Nat.sub_pos_of_lt hij
  have hord := hμ p.1 p.2 hij hj
  unfold rootDenominator
  linarith

/-- The full Weyl product of any weakly decreasing rows is strictly positive. -/
theorem activeProduct_pos_of_ordered (d : ℕ) (μ : ℕ → ℝ)
    (hμ : ∀ i j, i < j → j < d → μ j ≤ μ i) :
    0 < activeProduct d d μ := by
  unfold activeProduct
  apply Finset.prod_pos
  intro p hp
  apply div_pos (rootDenominator_pos_of_ordered d μ hμ p hp)
  exact_mod_cast Nat.sub_pos_of_lt (mem_activeRoots.mp hp).2.1

/-- Adding dominant rows increases every Weyl factor. -/
theorem activeProduct_mono_add_dominant (d : ℕ) (μ ω : ℕ → ℝ)
    (hμ : ∀ i j, i < j → j < d → μ j ≤ μ i)
    (hω : ∀ i j, i < j → j < d → ω j ≤ ω i) :
    activeProduct d d μ ≤ activeProduct d d (fun i => μ i + ω i) := by
  unfold activeProduct
  apply Finset.prod_le_prod
  · intro p hp
    exact le_of_lt (div_pos (rootDenominator_pos_of_ordered d μ hμ p hp)
      (by exact_mod_cast Nat.sub_pos_of_lt (mem_activeRoots.mp hp).2.1))
  · intro p hp
    apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
    have h := hω p.1 p.2 (mem_activeRoots.mp hp).2.1 (mem_activeRoots.mp hp).2.2
    linarith

/-- The actual ratio used by the matrix cloning theorem is in `(0,1]`.
No ratio-positivity or dimension-monotonicity assumption is needed. -/
theorem weyl_ratio_pos_le_one_from_rows (d : ℕ) (μ ω : ℕ → ℝ)
    (hμ : ∀ i j, i < j → j < d → μ j ≤ μ i)
    (hω : ∀ i j, i < j → j < d → ω j ≤ ω i) :
    0 < activeProduct d d μ / activeProduct d d (fun i => μ i + ω i) ∧
      activeProduct d d μ / activeProduct d d (fun i => μ i + ω i) ≤ 1 := by
  have hν : ∀ i j, i < j → j < d → μ j + ω j ≤ μ i + ω i := by
    intro i j hij hj
    exact add_le_add (hμ i j hij hj) (hω i j hij hj)
  have hposμ := activeProduct_pos_of_ordered d μ hμ
  have hposν := activeProduct_pos_of_ordered d (fun i => μ i + ω i) hν
  exact ⟨div_pos hposμ hposν, (div_le_one hposν).mpr
    (activeProduct_mono_add_dominant d μ ω hμ hω)⟩

/-- Values outside the dimension's row interval cannot affect the product. -/
theorem activeProduct_congr_rows (d r : ℕ) (μ ν : ℕ → ℝ)
    (h : ∀ i, i < d → μ i = ν i) : activeProduct d r μ = activeProduct d r ν := by
  unfold activeProduct
  apply Finset.prod_congr rfl
  intro p hp
  obtain ⟨_, hij, hj⟩ := mem_activeRoots.mp hp
  rw [h p.1 (hij.trans hj), h p.2 hj]

theorem weyl_ratio_eq_one_of_zero_rows (d : ℕ) (μ ω : ℕ → ℝ)
    (hμ : ∀ i j, i < j → j < d → μ j ≤ μ i)
    (hω : ∀ i, i < d → ω i = 0) :
    activeProduct d d μ / activeProduct d d (fun i => μ i + ω i) = 1 := by
  have heq : activeProduct d d (fun i => μ i + ω i) = activeProduct d d μ :=
    activeProduct_congr_rows d d _ _ (fun i hi => by rw [hω i hi, add_zero])
  rw [heq, div_self (activeProduct_pos_of_ordered d μ hμ).ne']

/-- The `D = 0` Weyl-ratio case follows from the actual L1 sum. -/
theorem weyl_ratio_eq_one_of_rowL1_zero (d : ℕ) (μ ω : ℕ → ℝ)
    (hμ : ∀ i j, i < j → j < d → μ j ≤ μ i) (hD : rowL1 d ω = 0) :
    activeProduct d d μ / activeProduct d d (fun i => μ i + ω i) = 1 :=
  weyl_ratio_eq_one_of_zero_rows d μ ω hμ ((rowL1_eq_zero_iff d ω).mp hD)

/-- Integrality justifies the paper's dichotomy `D = 0` or `D ≥ 1`,
without assuming that dichotomy as a separate quantitative hypothesis. -/
theorem rowL1_zero_or_one_le_of_integral (d : ℕ) (ω : ℕ → ℝ)
    (hintegral : ∀ i, i < d → ∃ z : ℤ, ω i = (z : ℝ)) :
    rowL1 d ω = 0 ∨ 1 ≤ rowL1 d ω := by
  classical
  by_cases hzero : rowL1 d ω = 0
  · exact Or.inl hzero
  right
  have hnot : ¬ ∀ i, i < d → ω i = 0 :=
    fun h => hzero ((rowL1_eq_zero_iff d ω).mpr h)
  obtain ⟨i, hi⟩ := not_forall.mp hnot
  obtain ⟨hid, hneq⟩ := Classical.not_imp.mp hi
  obtain ⟨z, hz⟩ := hintegral i hid
  have hz0 : z ≠ 0 := by
    intro heq
    apply hneq
    rw [hz, heq, Int.cast_zero]
  have hlarge : (1 : ℝ) ≤ |(z : ℝ)| := by
    rcases Int.cast_le_neg_one_or_one_le_cast_of_ne_zero ℝ hz0 with h | h
    · linarith [neg_le_abs (z : ℝ)]
    · exact h.trans (le_abs_self (z : ℝ))
  have hle : |ω i| ≤ rowL1 d ω :=
    Finset.single_le_sum (fun j _ => abs_nonneg (ω j)) (Finset.mem_range.mpr hid)
  rw [hz] at hle
  exact hlarge.trans hle

theorem rowL1_int_zero_or_one_le (d : ℕ) (ω : ℕ → ℤ) :
    rowL1 d (fun i => (ω i : ℝ)) = 0 ∨ 1 ≤ rowL1 d (fun i => (ω i : ℝ)) :=
  rowL1_zero_or_one_le_of_integral d _ (fun i _ => ⟨ω i, rfl⟩)

end FreeEntropy.Weyl
