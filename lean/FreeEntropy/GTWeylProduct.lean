/-
Copyright (c) 2026 Free Entropy formalization contributors.
See LICENSE and NOTICE in the repository root for license and attribution.
-/

import FreeEntropy.WeylCombinatorics
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fin.Rev

/-! Exact root-product reindexing used to identify the GT determinant with
the full and supported Weyl products. -/

noncomputable section
open scoped BigOperators

namespace FreeEntropy.GTDimension

def finRoots (n : ℕ) : Finset (Fin n × Fin n) :=
  Finset.univ.filter (fun p => p.1 < p.2)

theorem prod_finRoots {n : ℕ} {M : Type*} [CommMonoid M] (f : Fin n → Fin n → M) :
    (∏ p ∈ finRoots n, f p.1 p.2) = ∏ i : Fin n, ∏ j ∈ Finset.Ioi i, f i j := by
  rw [finRoots, Finset.prod_filter, ← Finset.univ_product_univ, Finset.prod_product]
  apply Finset.prod_congr rfl
  intro i _
  rw [← Finset.prod_filter]
  congr 1
  ext j
  simp

theorem prod_finRoots_reverse {n : ℕ} {M : Type*} [CommMonoid M] (f : ℕ × ℕ → M) :
    (∏ p ∈ finRoots n, f (p.2.rev.val, p.1.rev.val)) =
      ∏ p ∈ Weyl.activeRoots n n, f p := by
  apply Finset.prod_bij (fun p _ => (p.2.rev.val, p.1.rev.val))
  · intro p hp
    have hp' : p.1 < p.2 := (Finset.mem_filter.mp hp).2
    rw [Weyl.mem_activeRoots]
    exact ⟨p.2.rev.isLt, by change p.2.rev < p.1.rev; simpa using hp', p.1.rev.isLt⟩
  · intro a _ b _ he
    apply Prod.ext
    · have h : a.1.rev = b.1.rev := Fin.ext (Prod.mk.inj he).2
      simpa using congrArg Fin.rev h
    · have h : a.2.rev = b.2.rev := Fin.ext (Prod.mk.inj he).1
      simpa using congrArg Fin.rev h
  · intro q hq
    obtain ⟨h1, h12, h2⟩ := Weyl.mem_activeRoots.mp hq
    refine ⟨((⟨q.2, h2⟩ : Fin n).rev, (⟨q.1, h1⟩ : Fin n).rev), ?_, ?_⟩
    · apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, ?_⟩
      simpa using h12
    · simp
  · intro _ _
    rfl

theorem prod_activeRoots {M : Type*} [CommMonoid M] (d r : ℕ) (f : ℕ × ℕ → M) :
    (∏ p ∈ Weyl.activeRoots d r, f p) =
      ∏ i ∈ Finset.range r, ∏ j ∈ Finset.Ico (i + 1) d, f (i, j) := by
  rw [Weyl.activeRoots, Finset.prod_biUnion (Weyl.activeRoots_rows_disjoint d r)]
  apply Finset.prod_congr rfl
  intro i _
  rw [Finset.prod_image]
  intro a _ b _ h
  exact (Prod.mk.inj h).2

/-- The denominator of the full Weyl product is the product of the column factorials. -/
theorem full_denominator (n : ℕ) :
    (∏ p ∈ Weyl.activeRoots n n, ((p.2 - p.1 : ℕ) : ℝ)) =
      ∏ i : Fin n, ((i.val).factorial : ℝ) := by
  have hnat : (∏ p ∈ Weyl.activeRoots n n, (p.2 - p.1)) =
      ∏ i : Fin n, i.val.factorial := by
    rw [prod_activeRoots, Weyl.active_denominator n n le_rfl]
    simp only [Nat.sub_self, Nat.Ico_zero_eq_range, Fin.prod_univ_eq_prod_range]
  exact_mod_cast hnat

/-- Reversing the shifted Vandermonde numerator produces the exact Weyl root numerators. -/
theorem reversed_shifted_numerator (n : ℕ) (μ : ℕ → ℤ) :
    (∏ i : Fin n, ∏ j ∈ Finset.Ioi i,
      (((μ j.rev.val : ℝ) + (j.val : ℝ)) - ((μ i.rev.val : ℝ) + (i.val : ℝ)))) =
      ∏ p ∈ Weyl.activeRoots n n,
        ((μ p.1 : ℝ) - (μ p.2 : ℝ) + ((p.2 - p.1 : ℕ) : ℝ)) := by
  rw [← prod_finRoots]
  calc
    _ = ∏ p ∈ finRoots n,
        ((μ p.2.rev.val : ℝ) - (μ p.1.rev.val : ℝ) +
          ((p.1.rev.val - p.2.rev.val : ℕ) : ℝ)) := by
      apply Finset.prod_congr rfl
      intro p hp
      have hp' : p.1.val < p.2.val := (Finset.mem_filter.mp hp).2
      have hdiff : p.1.rev.val - p.2.rev.val = p.2.val - p.1.val := by
        have h1 := p.1.isLt
        have h2 := p.2.isLt
        simp only [Fin.val_rev]
        omega
      rw [hdiff, Nat.cast_sub (Nat.le_of_lt hp')]
      ring
    _ = _ := prod_finRoots_reverse (n := n) (fun p =>
      (μ p.1 : ℝ) - (μ p.2 : ℝ) + ((p.2 - p.1 : ℕ) : ℝ))

/-- Factors below the supported rank equal one, so the full and active Weyl products agree. -/
theorem full_product_eq_active (d r : ℕ) (hr : r ≤ d) (μ : ℕ → ℝ)
    (hzero : ∀ i, r ≤ i → i < d → μ i = 0) :
    Weyl.activeProduct d d μ = Weyl.activeProduct d r μ := by
  unfold Weyl.activeProduct
  symm
  apply Finset.prod_subset
  · intro p hp
    obtain ⟨h1, h12, h2⟩ := Weyl.mem_activeRoots.mp hp
    exact Weyl.mem_activeRoots.mpr ⟨lt_of_lt_of_le h1 hr, h12, h2⟩
  · intro p hp hn
    obtain ⟨h1, h12, h2⟩ := Weyl.mem_activeRoots.mp hp
    have hir : r ≤ p.1 := by
      by_contra h
      exact hn (Weyl.mem_activeRoots.mpr ⟨by omega, h12, h2⟩)
    rw [hzero p.1 hir h1, hzero p.2 (by omega) h2, sub_self, zero_add]
    exact div_self (by exact_mod_cast (Nat.sub_pos_of_lt h12).ne')

end FreeEntropy.GTDimension
