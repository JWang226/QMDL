/-
Copyright (c) 2026 Free Entropy formalization contributors.
See LICENSE and NOTICE in the repository root for license and attribution.
-/

import FreeEntropy.Statements
import FreeEntropy.WeylFinite

/-!
# Uniform estimates over the actual typical rows

The padded target is the manuscript's target. Typicality alone gives a
uniform linear supported gap and an explicit `O(log n / sqrt n)` bound for
the finite cloning envelope. Neither estimate is an additional asymptotic
hypothesis about the row family.
-/
noncomputable section
open Filter
open scoped BigOperators Topology

namespace FreeEntropy.TypicalRows

variable {d r : ℕ}

/-- Supported integral rows in the prescribed typical window. -/
def Typical (s : FixedSpectrum d r) (n : ℕ) (μ : ℕ → ℤ) : Prop :=
  (∀ i, i < r → |(μ i : ℝ) - (n : ℝ) * s.eigenvalue i| ≤ typicalWidth n) ∧
    ∀ i, r ≤ i → i < d → μ i = 0

def gapIndices (d r : ℕ) : Finset ℕ := (Finset.range r).filter (fun i => i + 1 < d)

theorem gapIndices_nonempty (s : FixedSpectrum d r) (hd : 2 ≤ d) :
    (gapIndices d r).Nonempty := ⟨0, by simp [gapIndices, s.rank_pos]; omega⟩

/-- A positive constant depending only on the fixed spectrum, including
its last positive-to-zero gap when the rank is deficient. -/
def minimumGap (s : FixedSpectrum d r) (hd : 2 ≤ d) : ℝ :=
  (gapIndices d r).inf' (gapIndices_nonempty s hd)
    (fun i => s.eigenvalue i - s.eigenvalue (i + 1))

theorem minimumGap_pos (s : FixedSpectrum d r) (hd : 2 ≤ d) :
    0 < minimumGap s hd := by
  apply (Finset.lt_inf'_iff _).mpr
  intro i hi
  obtain ⟨hi, hid⟩ := Finset.mem_filter.mp hi
  exact sub_pos.mpr (s.active_gap i (i + 1) (Finset.mem_range.mp hi) (by omega) hid)

theorem minimumGap_le (s : FixedSpectrum d r) (hd : 2 ≤ d)
    (i : ℕ) (hir : i < r) (hid : i + 1 < d) :
    minimumGap s hd ≤ s.eigenvalue i - s.eigenvalue (i + 1) :=
  Finset.inf'_le _ (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hir, hid⟩)

theorem width_nonneg (n : ℕ) (hn : 1 ≤ n) : 0 ≤ typicalWidth n := by
  apply mul_nonneg (Real.sqrt_nonneg _)
  exact Real.logb_nonneg (by norm_num) (by exact_mod_cast hn)

theorem typical_gap (s : FixedSpectrum d r) (hd : 2 ≤ d)
    (n : ℕ) (hn : 1 ≤ n) (μ : ℕ → ℤ) (hμ : Typical s n μ)
    (i : ℕ) (hir : i < r) (hid : i + 1 < d) :
    (n : ℝ) * minimumGap s hd - 2 * typicalWidth n ≤
      (μ i : ℝ) - (μ (i + 1) : ℝ) := by
  have ha := hμ.1 i hir
  have hb : |(μ (i + 1) : ℝ) - (n : ℝ) * s.eigenvalue (i + 1)| ≤ typicalWidth n := by
    by_cases hj : i + 1 < r
    · exact hμ.1 _ hj
    · rw [hμ.2 _ (by omega) hid, s.zero_padded _ (by omega) hid]
      simpa using width_nonneg n hn
  have hg := typical_gap_lower ha hb
  have hm := mul_le_mul_of_nonneg_left (minimumGap_le s hd i hir hid) (Nat.cast_nonneg n)
  linarith

/-- Every supported adjacent gap is uniformly linear in `n`, simultaneously
for every typical row. -/
theorem eventually_uniform_gap (s : FixedSpectrum d r) (hd : 2 ≤ d) :
    ∀ᶠ n in atTop, ∀ μ, Typical s n μ → ∀ i, i < r → i + 1 < d →
      (n : ℝ) * minimumGap s hd / 2 ≤ (μ i : ℝ) - (μ (i + 1) : ℝ) := by
  have he := typicalWidth_div_tendsto_zero.eventually
    (gt_mem_nhds (show (0 : ℝ) < minimumGap s hd / 4 by linarith [minimumGap_pos s hd]))
  filter_upwards [he, eventually_ge_atTop 1] with n he hn
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hw := (div_lt_iff₀ hn0).mp he
  intro μ hμ i hir hid
  have hg := typical_gap s hd n hn μ hμ i hir hid
  nlinarith

/-- A bound on each target surplus, uniform over the typical window. -/
theorem row_surplus_bounds (s : FixedSpectrum d r) (n : ℕ) (hn : 1 ≤ n)
    (μ : ℕ → ℤ) (hμ : Typical s n μ) (i : ℕ) (hi : i < r) :
    0 ≤ s.targetRow n i - (μ i : ℝ) ∧
      s.targetRow n i - (μ i : ℝ) ≤
        (2 * (r : ℝ) + 1) * typicalWidth n + r + 1 := by
  have hε := width_nonneg n hn
  have htyp := abs_le.mp (hμ.1 i hi)
  have hk : (1 : ℝ) ≤ (r - i : ℕ) := by exact_mod_cast (show 1 ≤ r - i by omega)
  have hkr : ((r - i : ℕ) : ℝ) ≤ r := by exact_mod_cast Nat.sub_le r i
  have hlow := Int.le_ceil ((n : ℝ) * s.eigenvalue i + (r - i : ℕ) * (2 * typicalWidth n + 1))
  have hupp := Int.ceil_lt_add_one ((n : ℝ) * s.eigenvalue i + (r - i : ℕ) * (2 * typicalWidth n + 1))
  simp only [FixedSpectrum.targetRow, hi, ↓reduceIte, paddedRow]
  constructor <;> nlinarith

/-- Adjacent dominance suffices on the finite ambient range. -/
theorem dominant_of_adjacent {ω : ℕ → ℝ}
    (hω : ∀ i, i + 1 < d → ω (i + 1) ≤ ω i) :
    ∀ i j, i < j → j < d → ω j ≤ ω i := by
  intro i j hij hj
  have haux : ∀ k, i ≤ k → k < d → ω k ≤ ω i := by
    intro k hik
    induction hik with
    | refl => intro _; exact le_rfl
    | @step k hik ih =>
      intro hk
      exact (hω k hk).trans (ih (by omega))
  exact haux j hij.le hj

/-- Padding makes the target-minus-source difference dominant for every
actual typical row, including across the supported-to-zero boundary. -/
theorem target_difference_dominant (s : FixedSpectrum d r) (n : ℕ) (hn : 1 ≤ n)
    (μ : ℕ → ℤ) (hμ : Typical s n μ) :
    ∀ i j, i < j → j < d →
      s.targetRow n j - (μ j : ℝ) ≤ s.targetRow n i - (μ i : ℝ) := by
  apply dominant_of_adjacent
  intro i hid
  by_cases hj : i + 1 < r
  · have hi : i < r := by omega
    have hk : ((r - i : ℕ) : ℝ) = ((r - (i + 1) : ℕ) : ℝ) + 1 := by
      have hnat : r - i = (r - (i + 1)) + 1 := by omega
      exact_mod_cast hnat
    have h := padded_difference_dominant ((r - (i + 1) : ℕ) : ℝ)
      (hμ.1 i hi) (hμ.1 (i + 1) hj)
    simpa only [FixedSpectrum.targetRow, hi, hj, ↓reduceIte, hk] using h
  · have hzj := hμ.2 (i + 1) (by omega) hid
    by_cases hi : i < r
    · simpa only [FixedSpectrum.targetRow, hj, ↓reduceIte, hzj, Int.cast_zero, sub_zero]
        using (row_surplus_bounds s n hn μ hμ i hi).1
    · have hzi := hμ.2 i (by omega) (by omega)
      simp [FixedSpectrum.targetRow, hi, hj, hzi, hzj]

/-- The actual L1 distance to the padded target is uniformly controlled. -/
theorem rowL1_le (s : FixedSpectrum d r) (n : ℕ) (hn : 1 ≤ n)
    (μ : ℕ → ℤ) (hμ : Typical s n μ) :
    Weyl.rowL1 d (fun i => s.targetRow n i - (μ i : ℝ)) ≤
      (r : ℝ) * ((2 * (r : ℝ) + 1) * typicalWidth n + r + 1) := by
  have hsum : Weyl.rowL1 d (fun i => s.targetRow n i - (μ i : ℝ)) =
      ∑ i ∈ Finset.range r, |s.targetRow n i - (μ i : ℝ)| := by
    unfold Weyl.rowL1
    symm
    apply Finset.sum_subset (Finset.range_mono s.rank_le)
    intro i hid hir
    have hi : ¬ i < r := by simpa using hir
    simp [FixedSpectrum.targetRow, hi, hμ.2 i (by omega) (Finset.mem_range.mp hid)]
  rw [hsum]
  calc
    _ ≤ ∑ _i ∈ Finset.range r,
        ((2 * (r : ℝ) + 1) * typicalWidth n + r + 1) := by
      apply Finset.sum_le_sum
      intro i hi
      obtain ⟨h0, hb⟩ := row_surplus_bounds s n hn μ hμ i (Finset.mem_range.mp hi)
      simpa only [abs_of_nonneg h0] using hb
    _ = _ := by simp; ring

/-- The exact width is at most `n` times the claimed error rate. -/
theorem width_le_scaled_error (n : ℕ) (hn : 2 ≤ n) :
    typicalWidth n ≤ (n : ℝ) * Weyl.errorScale n := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hl : 0 ≤ Real.logb 2 n := Real.logb_nonneg (by norm_num) (by exact_mod_cast (show 1 ≤ n by omega))
  have hs : 0 < Real.sqrt n := Real.sqrt_pos.mpr hn0
  have he : (n : ℝ) * Weyl.errorScale n = Real.sqrt n * Real.logb 2 n := by
    unfold Weyl.errorScale
    rw [← mul_div_assoc]
    apply (div_eq_iff hs.ne').mpr
    nlinarith [Real.sq_sqrt hn0.le]
  rw [he]
  exact mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt (by linarith)) hl

/-- Explicit uniform distance bound on the scale used in Theorem 1. -/
theorem rowL1_le_scaled_error (s : FixedSpectrum d r) (n : ℕ) (hn : 2 ≤ n)
    (μ : ℕ → ℤ) (hμ : Typical s n μ) :
    Weyl.rowL1 d (fun i => s.targetRow n i - (μ i : ℝ)) ≤
      ((r : ℝ) * (3 * r + 2)) * ((n : ℝ) * Weyl.errorScale n) := by
  have h := rowL1_le s n (by omega) μ hμ
  have he := width_le_scaled_error n hn
  have hi := Concentration.inv_le_errorScale n hn
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have h1 : 1 ≤ (n : ℝ) * Weyl.errorScale n := by
    have hh := (div_le_iff₀ hn0).mp hi
    simpa only [Weyl.errorScale, mul_comm] using hh
  have hr : (0 : ℝ) ≤ r := Nat.cast_nonneg r
  have hscaled := mul_le_mul_of_nonneg_left he (show 0 ≤ 2 * (r : ℝ) + 1 by positivity)
  have hconst := mul_le_mul_of_nonneg_left h1 (show 0 ≤ (r : ℝ) + 1 by positivity)
  have hinner : (2 * (r : ℝ) + 1) * typicalWidth n + r + 1 ≤
      (3 * (r : ℝ) + 2) * ((n : ℝ) * Weyl.errorScale n) := by nlinarith
  have hh := mul_le_mul_of_nonneg_left hinner hr
  nlinarith

/-- The actual finite cloning envelope has the claimed rate uniformly over
all typical rows. `C` is the fixed cloning constant from Theorem 2. -/
theorem cloning_envelope_le (s : FixedSpectrum d r) (hd : 2 ≤ d)
    (C : ℝ) (hC : 0 ≤ C) (n : ℕ) (hn : 2 ≤ n)
    (μ : ℕ → ℤ) (hμ : Typical s n μ) :
    C * Weyl.rowL1 d (fun i => s.targetRow n i - (μ i : ℝ)) /
      ((n : ℝ) * minimumGap s hd / 2 + 1) ≤
      (2 * C * ((r : ℝ) * (3 * r + 2)) / minimumGap s hd) * Weyl.errorScale n := by
  have hβ := minimumGap_pos s hd
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hr : 0 ≤ Weyl.errorScale n := by
    unfold Weyl.errorScale
    exact div_nonneg (Real.logb_nonneg (by norm_num) (by exact_mod_cast (show 1 ≤ n by omega))) (Real.sqrt_nonneg _)
  have hB : 0 ≤ (r : ℝ) * (3 * r + 2) := by positivity
  have hD := mul_le_mul_of_nonneg_left (rowL1_le_scaled_error s n hn μ hμ) hC
  apply (div_le_iff₀ (show 0 < (n : ℝ) * minimumGap s hd / 2 + 1 by positivity)).mpr
  have he : (2 * C * ((r : ℝ) * (3 * r + 2)) / minimumGap s hd) * Weyl.errorScale n *
      ((n : ℝ) * minimumGap s hd / 2) =
      C * (((r : ℝ) * (3 * r + 2)) * ((n : ℝ) * Weyl.errorScale n)) := by
    field_simp
  have h0 : 0 ≤ (2 * C * ((r : ℝ) * (3 * r + 2)) / minimumGap s hd) * Weyl.errorScale n := by positivity
  nlinarith

end FreeEntropy.TypicalRows
