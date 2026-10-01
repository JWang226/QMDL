/-
Copyright (c) 2026 Free Entropy formalization contributors.
See LICENSE and NOTICE in the repository root for license and attribution.
-/

import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The exact mean-depth majorant in Theorem 2

The analytic generating-series calculation is proved here. The Kostant/Verma
multiplicity estimate is an explicit hypothesis of the finite-sector bound.
-/

open scoped BigOperators

namespace FreeEntropy.MeanDepth

/-- The explicit constant called `K(x)` in the paper, with `q = q_x` and
`N = r.choose 2`. -/
noncomputable def meanDepthConstant (N : ℕ) (q : ℝ) : ℝ :=
  (N : ℝ) * q / (1 - q) ^ (N + 1)

theorem meanDepthConstant_nonneg (N : ℕ) (q : ℝ) (hq : 0 ≤ q) (hq1 : q < 1) :
    0 ≤ meanDepthConstant N q := by
  unfold meanDepthConstant
  exact div_nonneg (mul_nonneg (Nat.cast_nonneg _) hq) (pow_nonneg (by linarith) _)

@[simp] theorem meanDepthConstant_zero (q : ℝ) : meanDepthConstant 0 q = 0 := by
  simp [meanDepthConstant]

/-- The coefficient identity replacing formal differentiation of the
negative-binomial generating function. -/
theorem first_moment_coefficient (t N : ℕ) (hN : 0 < N) :
    t * (t + N - 1).choose (N - 1) = N * (t + N - 1).choose N := by
  have h := Nat.choose_succ_right_eq (t + N - 1) (N - 1)
  have hsucc : N - 1 + 1 = N := by omega
  have hsub : t + N - 1 - (N - 1) = t := by omega
  simpa only [hsucc, hsub, Nat.mul_comm] using h.symm

/-- A monomial in adjacent eigenvalue ratios is bounded by `q` to its
simple-root depth when all those ratios are at most `q`. -/
theorem root_monomial_le {ι : Type*} (s : Finset ι) (c : ι → ℕ)
    (ratio : ι → ℝ) (q : ℝ)
    (hratio : ∀ i ∈ s, 0 ≤ ratio i) (hbound : ∀ i ∈ s, ratio i ≤ q) :
    ∏ i ∈ s, ratio i ^ c i ≤ q ^ (∑ i ∈ s, c i) := by
  calc
    _ ≤ ∏ i ∈ s, q ^ c i := Finset.prod_le_prod
      (fun i hi => pow_nonneg (hratio i hi) _)
      (fun i hi => pow_le_pow_left₀ (hratio i hi) (hbound i hi) _)
    _ = _ := Finset.prod_pow_eq_pow_sum _ _ _

/-- Including the Schur normalizer cannot increase this envelope if the
normalizer divided by its highest-weight term is at least one. -/
theorem normalized_root_monomial_le {ι : Type*} (s : Finset ι) (c : ι → ℕ)
    (ratio : ι → ℝ) (q normalizer : ℝ)
    (hratio : ∀ i ∈ s, 0 ≤ ratio i) (hbound : ∀ i ∈ s, ratio i ≤ q)
    (hnormalizer : 1 ≤ normalizer) :
    (∏ i ∈ s, ratio i ^ c i) / normalizer ≤ q ^ (∑ i ∈ s, c i) := by
  exact (div_le_self (Finset.prod_nonneg (fun i hi => pow_nonneg (hratio i hi) _))
    hnormalizer).trans (root_monomial_le s c ratio q hratio hbound)

/-- The exact convergent first-moment series used in the uniform depth bound. -/
theorem hasSum_first_moment (N : ℕ) (hN : 0 < N) (q : ℝ)
    (hq : 0 ≤ q) (hq1 : q < 1) :
    HasSum (fun t : ℕ => (t : ℝ) * ((t + N - 1).choose (N - 1) : ℝ) * q ^ t)
      (meanDepthConstant N q) := by
  have hnorm : ‖q‖ < 1 := by simpa only [Real.norm_eq_abs, abs_of_nonneg hq] using hq1
  have h : HasSum (fun t : ℕ => ((N : ℝ) * q) * (((t + N).choose N : ℝ) * q ^ t))
      (((N : ℝ) * q) * (1 / (1 - q) ^ (N + 1))) :=
    (hasSum_choose_mul_geometric_of_norm_lt_one N hnorm).mul_left ((N : ℝ) * q)
  have hshift : HasSum (fun t : ℕ => ((t + 1 : ℕ) : ℝ) *
      ((t + 1 + N - 1).choose (N - 1) : ℝ) * q ^ (t + 1))
      (meanDepthConstant N q) := by
    convert h using 1
    · ext t
      rw [← Nat.cast_mul, first_moment_coefficient (t + 1) N hN]
      have ht : t + 1 + N - 1 = t + N := by omega
      rw [ht, Nat.cast_mul, pow_succ]
      ring
    · unfold meanDepthConstant
      ring
  simpa using (hasSum_nat_add_iff
    (f := fun t : ℕ => (t : ℝ) * ((t + N - 1).choose (N - 1) : ℝ) * q ^ t) 1).mp hshift

/-- Any finite depth distribution dominated by the negative-binomial envelope
has the paper's uniform mean bound. -/
theorem finite_mean_le (T : Finset ℕ) (mass : ℕ → ℝ) (N : ℕ)
    (hN : 0 < N) (q : ℝ) (hq : 0 ≤ q) (hq1 : q < 1)
    (hmass : ∀ t ∈ T, mass t ≤ ((t + N - 1).choose (N - 1) : ℝ) * q ^ t) :
    ∑ t ∈ T, (t : ℝ) * mass t ≤ meanDepthConstant N q := by
  calc
    _ ≤ ∑ t ∈ T, (t : ℝ) * ((t + N - 1).choose (N - 1) : ℝ) * q ^ t := by
      apply Finset.sum_le_sum
      intro t ht
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_left (hmass t ht) (Nat.cast_nonneg t : (0 : ℝ) ≤ t)
    _ ≤ _ := sum_le_hasSum T (fun t _ => by positivity) (hasSum_first_moment N hN q hq hq1)

/-- The uniform mean-depth lemma for a finite set of weight offsets. The
Verma/Kostant bound is precisely `hmult`; the spectral envelope is `hp`.
The summation, regrouping by integer depth, and exact constant are proved. -/
theorem weight_mean_le {ι : Type*} (s : Finset ι) (depth mult : ι → ℕ)
    (p : ι → ℝ) (N : ℕ) (hN : 0 < N) (q : ℝ)
    (hq : 0 ≤ q) (hq1 : q < 1)
    (hp : ∀ i ∈ s, p i ≤ q ^ depth i)
    (hmult : ∀ t, ∑ i ∈ s with depth i = t, mult i ≤ (t + N - 1).choose (N - 1)) :
    ∑ i ∈ s, (depth i : ℝ) * p i * (mult i : ℝ) ≤ meanDepthConstant N q := by
  classical
  let mass : ℕ → ℝ := fun t => ∑ i ∈ s with depth i = t, p i * (mult i : ℝ)
  have hmass (t : ℕ) : mass t ≤ ((t + N - 1).choose (N - 1) : ℝ) * q ^ t := by
    calc
      mass t ≤ ∑ i ∈ s with depth i = t, q ^ t * (mult i : ℝ) := by
        apply Finset.sum_le_sum
        intro i hi
        obtain ⟨his, hit⟩ := Finset.mem_filter.mp hi
        apply mul_le_mul_of_nonneg_right _ (Nat.cast_nonneg _)
        simpa only [hit] using hp i his
      _ = q ^ t * ∑ i ∈ s with depth i = t, (mult i : ℝ) := (Finset.mul_sum _ _ _).symm
      _ ≤ q ^ t * ((t + N - 1).choose (N - 1) : ℝ) := by
        apply mul_le_mul_of_nonneg_left _ (pow_nonneg hq _)
        exact_mod_cast hmult t
      _ = _ := mul_comm _ _
  have hregroup : (∑ t ∈ s.image depth, (t : ℝ) * mass t) =
      ∑ i ∈ s, (depth i : ℝ) * p i * (mult i : ℝ) := by
    calc
      _ = ∑ t ∈ s.image depth, ∑ i ∈ s with depth i = t,
          (depth i : ℝ) * p i * (mult i : ℝ) := by
        apply Finset.sum_congr rfl
        intro t _
        dsimp only [mass]
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i hi
        rw [(Finset.mem_filter.mp hi).2]
        ring
      _ = _ := Finset.sum_fiberwise_of_maps_to
        (fun i hi => Finset.mem_image.mpr ⟨i, hi, rfl⟩) _
  rw [← hregroup]
  exact finite_mean_le (s.image depth) mass N hN q hq hq1 (fun t _ => hmass t)

end FreeEntropy.MeanDepth
