/-
Copyright (c) 2026 Free Entropy formalization contributors.
See LICENSE and NOTICE in the repository root for license and attribution.
-/

import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Typical and atypical errors in the compression protocol

The input errors in this module are real numbers. Applying these results to
quantum trace distance requires the convexity, block sum, and contractivity
estimates displayed in equations `error_triangle` and `error_twoterms` of
the paper. No quantum interpretation is imposed by definition.
-/

noncomputable section
open Filter
open scoped BigOperators Topology
namespace FreeEntropy.Protocol

def outsideMass {ι : Type*} [DecidableEq ι] (s t : Finset ι) (q : ι → ℝ) : ℝ :=
  ∑ i ∈ s, if i ∈ t then 0 else q i

theorem weighted_error_le {ι : Type*} [DecidableEq ι]
    (s t : Finset ι) (q err : ι → ℝ) (ε : ℝ)
    (hq : ∀ i ∈ s, 0 ≤ q i) (hsum : ∑ i ∈ s, q i = 1)
    (hε : 0 ≤ ε) (htyp : ∀ i ∈ s, i ∈ t → err i ≤ ε)
    (hmax : ∀ i ∈ s, err i ≤ 1) :
    ∑ i ∈ s, q i * err i ≤ ε + outsideMass s t q := by
  calc
    _ ≤ ∑ i ∈ s, (q i * ε + if i ∈ t then 0 else q i) := by
      apply Finset.sum_le_sum
      intro i hi
      by_cases hit : i ∈ t
      · simpa [hit] using mul_le_mul_of_nonneg_left (htyp i hi hit) (hq i hi)
      · simp only [hit, ↓reduceIte]
        have h := mul_le_mul_of_nonneg_left (hmax i hi) (hq i hi)
        have h' := mul_nonneg (hq i hi) hε
        nlinarith
    _ = ε + outsideMass s t q := by
      rw [Finset.sum_add_distrib, ← Finset.sum_mul, hsum, one_mul]
      rfl

/-- The factor two in the atypical tail is necessary because both the
forward and reverse error averages occur. -/
theorem roundtrip_error_le {ι : Type*} [DecidableEq ι]
    (s t : Finset ι) (q forward reverse : ι → ℝ) (ε δ : ℝ)
    (hq : ∀ i ∈ s, 0 ≤ q i) (hsum : ∑ i ∈ s, q i = 1)
    (hε : 0 ≤ ε)
    (hf : ∀ i ∈ s, i ∈ t → forward i ≤ ε)
    (hr : ∀ i ∈ s, i ∈ t → reverse i ≤ ε)
    (hf1 : ∀ i ∈ s, forward i ≤ 1) (hr1 : ∀ i ∈ s, reverse i ≤ 1)
    (hδ : δ ≤ (∑ i ∈ s, q i * forward i) + ∑ i ∈ s, q i * reverse i) :
    δ ≤ 2 * ε + 2 * outsideMass s t q := by
  have hf' := weighted_error_le s t q forward ε hq hsum hε hf hf1
  have hr' := weighted_error_le s t q reverse ε hq hsum hε hr hr1
  linarith

/-- Convert the finite estimates into the asymptotic error claim. -/
theorem error_isBigO {δ ε tail rate : ℕ → ℝ} {C T : ℝ}
    (hδ0 : ∀ᶠ n in atTop, 0 ≤ δ n)
    (hrate : ∀ᶠ n in atTop, 0 ≤ rate n)
    (hδ : ∀ᶠ n in atTop, δ n ≤ 2 * ε n + 2 * tail n)
    (hε : ∀ᶠ n in atTop, ε n ≤ C * rate n)
    (htail : ∀ᶠ n in atTop, tail n ≤ T * rate n) :
    Asymptotics.IsBigO atTop δ rate := by
  apply Asymptotics.IsBigO.of_bound (2 * C + 2 * T)
  filter_upwards [hδ0, hrate, hδ, hε, htail] with n hn0 hnr hn he ht
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hn0, abs_of_nonneg hnr]
  nlinarith

end FreeEntropy.Protocol
