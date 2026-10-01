/-
Copyright (c) 2026 Free Entropy formalization contributors.
See LICENSE and NOTICE in the repository root for license and attribution.
-/

import FreeEntropy.MeanDepth
import FreeEntropy.CloningMatrices

/-!
# Normalized weight coefficients and a uniform spectral gap

The coefficients are defined by an actual finite partition function. The
highest-weight contribution proves the lower bound on this normalizer;
normalization, common eigenvalue ratio, and geometric spectral envelopes
are then consequences, rather than input inequalities.
-/

noncomputable section
open scoped BigOperators
namespace FreeEntropy.WeightNormalization
set_option linter.unusedSectionVars false

variable {ι : Type*}

def partitionFunction (s : Finset ι) (mult : ι → ℕ) (w : ι → ℝ) : ℝ :=
  ∑ i ∈ s, w i * (mult i : ℝ)

def coefficient (s : Finset ι) (mult : ι → ℕ) (w : ι → ℝ) (i : ι) : ℝ :=
  w i / partitionFunction s mult w

/-- The highest-weight line contributes exactly one to the normalizer. -/
theorem partitionFunction_ge_one (s : Finset ι) (mult : ι → ℕ) (w : ι → ℝ)
    (hw : ∀ i ∈ s, 0 ≤ w i) (i₀ : ι) (hi₀ : i₀ ∈ s)
    (hm₀ : mult i₀ = 1) (hw₀ : w i₀ = 1) :
    1 ≤ partitionFunction s mult w := by
  have h := Finset.single_le_sum
    (fun i hi => mul_nonneg (hw i hi) (Nat.cast_nonneg (mult i))) hi₀
  simpa [partitionFunction, hm₀, hw₀] using h

theorem coefficient_nonneg (s : Finset ι) (mult : ι → ℕ) (w : ι → ℝ)
    (hw : ∀ i ∈ s, 0 ≤ w i) (hZ : 0 < partitionFunction s mult w)
    (i : ι) (hi : i ∈ s) : 0 ≤ coefficient s mult w i :=
  div_nonneg (hw i hi) hZ.le

/-- The normalized coefficients sum to one with their actual multiplicities. -/
theorem coefficient_normalized (s : Finset ι) (mult : ι → ℕ) (w : ι → ℝ)
    (hZ : partitionFunction s mult w ≠ 0) :
    ∑ i ∈ s, coefficient s mult w i * (mult i : ℝ) = 1 := by
  unfold coefficient
  simp_rw [div_mul_eq_mul_div]
  rw [← Finset.sum_div]
  exact div_self hZ

/-- Changing the multiplicities changes all coefficients by the same ratio. -/
theorem coefficient_ratio (s : Finset ι) (m n : ι → ℕ) (w : ι → ℝ)
    (hZm : partitionFunction s m w ≠ 0) (i : ι) :
    coefficient s n w i = (partitionFunction s m w / partitionFunction s n w) *
      coefficient s m w i := by
  unfold coefficient
  by_cases hZn : partitionFunction s n w = 0
  · simp [hZn]
  · field_simp

theorem coefficient_le_geometric (s : Finset ι) (mult depth : ι → ℕ)
    (w : ι → ℝ) (q : ℝ) (hw : ∀ i ∈ s, 0 ≤ w i)
    (hZ : 1 ≤ partitionFunction s mult w)
    (henvelope : ∀ i ∈ s, w i ≤ q ^ depth i) (i : ι) (hi : i ∈ s) :
    coefficient s mult w i ≤ q ^ depth i :=
  (div_le_self (hw i hi) hZ).trans (henvelope i hi)

/-- A root monomial supplies the spectral envelope automatically. -/
theorem coefficient_root_envelope {κ : Type*} (s : Finset ι) (roots : Finset κ)
    (mult : ι → ℕ) (c : ι → κ → ℕ) (ratio : κ → ℝ) (q : ℝ)
    (hratio : ∀ j ∈ roots, 0 ≤ ratio j) (hbound : ∀ j ∈ roots, ratio j ≤ q)
    (hZ : 1 ≤ partitionFunction s mult (fun i => ∏ j ∈ roots, ratio j ^ c i j))
    (i : ι) :
    coefficient s mult (fun i => ∏ j ∈ roots, ratio j ^ c i j) i ≤
      q ^ (∑ j ∈ roots, c i j) :=
  MeanDepth.normalized_root_monomial_le roots (c i) ratio q _ hratio hbound hZ

/-- The zeroth-moment geometric series used for a uniform spectral gap. -/
theorem hasSum_partition_majorant (N : ℕ) (hN : 0 < N) (q : ℝ)
    (hq : 0 ≤ q) (hq1 : q < 1) :
    HasSum (fun t : ℕ => ((t + N - 1).choose (N - 1) : ℝ) * q ^ t)
      (1 / (1 - q) ^ N) := by
  have hnorm : ‖q‖ < 1 := by simpa [Real.norm_eq_abs, abs_of_nonneg hq] using hq1
  have h := hasSum_choose_mul_geometric_of_norm_lt_one (N - 1) hnorm
  convert h using 1
  · ext t
    congr 3
    omega
  · congr 2
    omega

/-- The multiplicity envelope bounds the actual normalizer, including its
highest-weight term. This provides a uniform positive spectral gap without
assuming the manuscript's sharper product formula for the top eigenvalue. -/
theorem partitionFunction_le (s : Finset ι) (depth mult : ι → ℕ)
    (w : ι → ℝ) (N : ℕ) (hN : 0 < N) (q : ℝ) (hq : 0 ≤ q) (hq1 : q < 1)
    (hw : ∀ i ∈ s, w i ≤ q ^ depth i)
    (hmult : ∀ t, ∑ i ∈ s with depth i = t, mult i ≤
      (t + N - 1).choose (N - 1)) :
    partitionFunction s mult w ≤ 1 / (1 - q) ^ N := by
  classical
  calc
    _ = ∑ t ∈ s.image depth, ∑ i ∈ s with depth i = t, w i * (mult i : ℝ) :=
      (Finset.sum_fiberwise_of_maps_to (fun i hi => Finset.mem_image.mpr ⟨i, hi, rfl⟩) _).symm
    _ ≤ ∑ t ∈ s.image depth, ((t + N - 1).choose (N - 1) : ℝ) * q ^ t := by
      apply Finset.sum_le_sum
      intro t _
      calc
        _ ≤ ∑ i ∈ s with depth i = t, q ^ t * (mult i : ℝ) := by
          apply Finset.sum_le_sum
          intro i hi
          obtain ⟨his, hit⟩ := Finset.mem_filter.mp hi
          exact mul_le_mul_of_nonneg_right (by simpa [hit] using hw i his) (Nat.cast_nonneg _)
        _ = q ^ t * ∑ i ∈ s with depth i = t, (mult i : ℝ) := (Finset.mul_sum _ _ _).symm
        _ ≤ q ^ t * ((t + N - 1).choose (N - 1) : ℝ) := by
          exact mul_le_mul_of_nonneg_left (by exact_mod_cast hmult t) (pow_nonneg hq _)
        _ = _ := mul_comm _ _
    _ ≤ _ := sum_le_hasSum _ (fun t _ => by positivity) (hasSum_partition_majorant N hN q hq hq1)

/-- A uniform lower bound on the normalized highest-weight eigenvalue. -/
theorem top_coefficient_lower (s : Finset ι) (mult : ι → ℕ) (w : ι → ℝ)
    (N : ℕ) (q : ℝ) (hq1 : q < 1)
    (hZ : 0 < partitionFunction s mult w)
    (hupper : partitionFunction s mult w ≤ 1 / (1 - q) ^ N) :
    (1 - q) ^ N ≤ 1 / partitionFunction s mult w := by
  have hpow : 0 < (1 - q) ^ N := pow_pos (by linarith) _
  apply (le_div_iff₀ hZ).mpr
  have h := (le_div_iff₀ hpow).mp hupper
  nlinarith

/-- A nonzero depth bounds every non-highest coefficient by `q` times the
highest coefficient. -/
theorem next_coefficient_upper (s : Finset ι) (depth mult : ι → ℕ) (w : ι → ℝ)
    (q : ℝ) (hq : 0 ≤ q) (hq1 : q ≤ 1) (hZ : 0 < partitionFunction s mult w)
    (i : ι) (hi : 1 ≤ depth i) (hw : w i ≤ q ^ depth i) :
    coefficient s mult w i ≤ q * (1 / partitionFunction s mult w) := by
  have hpow : q ^ depth i ≤ q := by
    obtain ⟨t, ht⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : depth i ≠ 0)
    rw [ht, pow_succ]
    have hp : q ^ t ≤ 1 := pow_le_one₀ hq hq1
    nlinarith
  unfold coefficient
  simpa only [mul_one_div] using div_le_div_of_nonneg_right (hw.trans hpow) hZ.le

/-- The weaker but sufficient fixed gap `(1-q)^(N+1)` is now proved. -/
theorem uniform_gap (s : Finset ι) (mult : ι → ℕ) (w : ι → ℝ)
    (N : ℕ) (q : ℝ) (hq1 : q < 1)
    (hZ : 0 < partitionFunction s mult w)
    (hupper : partitionFunction s mult w ≤ 1 / (1 - q) ^ N) :
    0 < (1 - q) ^ (N + 1) ∧
      (1 - q) ^ (N + 1) ≤
        1 / partitionFunction s mult w - q * (1 / partitionFunction s mult w) := by
  have htop := top_coefficient_lower s mult w N q hq1 hZ hupper
  constructor
  · exact pow_pos (by linarith) _
  · rw [pow_succ]
    nlinarith [mul_le_mul_of_nonneg_right htop (by linarith : 0 ≤ 1 - q)]

end FreeEntropy.WeightNormalization
