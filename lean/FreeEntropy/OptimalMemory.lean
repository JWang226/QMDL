/-
Copyright (c) 2026 Free Entropy formalization contributors.
See LICENSE and NOTICE in the repository root for license and attribution.
-/

import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Topology.Instances.EReal.Lemmas
import Mathlib.Order.LiminfLimsup
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

/-!
# Scalar parts of Theorem 1 (optimal memory cost)

This file verifies the target-padding arithmetic and the asymptotic converse
after the quantum/representation-theoretic estimates have been supplied as
explicit hypotheses.  It does not assert those missing estimates as axioms.
All logarithms in memory costs are `Real.logb 2`.
-/

namespace FreeEntropy

open Filter
open scoped Topology BigOperators

/-- A padded row, with `k = r-i+1` in the manuscript's one-based indexing. -/
noncomputable def paddedRow (n x ε k : ℝ) : ℤ :=
  ⌈n * x + k * (2 * ε + 1)⌉

/-- The rounding estimate used to make the target difference dominant. -/
theorem paddedRow_gap (n x y ε k : ℝ) :
    n * (x - y) + 2 * ε ≤
      (paddedRow n x ε (k + 1) : ℝ) - (paddedRow n y ε k : ℝ) := by
  have h₁ := Int.le_ceil (n * x + (k + 1) * (2 * ε + 1))
  have h₂ := Int.ceil_lt_add_one (n * y + k * (2 * ε + 1))
  dsimp [paddedRow]
  nlinarith

/-- Typicality gives the upper adjacent-gap estimate used by padding. -/
theorem typical_gap_upper {n x y ε a b : ℝ}
    (ha : |a - n * x| ≤ ε) (hb : |b - n * y| ≤ ε) :
    a - b ≤ n * (x - y) + 2 * ε := by
  rcases abs_le.mp ha with ⟨ha₁, ha₂⟩
  rcases abs_le.mp hb with ⟨hb₁, hb₂⟩
  nlinarith

/-- The lower gap estimate explains the linear row-gap lower bound. -/
theorem typical_gap_lower {n x y ε a b : ℝ}
    (ha : |a - n * x| ≤ ε) (hb : |b - n * y| ≤ ε) :
    n * (x - y) - 2 * ε ≤ a - b := by
  rcases abs_le.mp ha with ⟨ha₁, ha₂⟩
  rcases abs_le.mp hb with ⟨hb₁, hb₂⟩
  nlinarith

/-- Adjacent rows of the padded target minus a typical partition decrease. -/
theorem padded_difference_dominant {n x y ε a b : ℝ} (k : ℝ)
    (ha : |a - n * x| ≤ ε) (hb : |b - n * y| ≤ ε) :
    (paddedRow n y ε k : ℝ) - b ≤
      (paddedRow n x ε (k + 1) : ℝ) - a := by
  have hgap := paddedRow_gap n x y ε k
  have htyp := typical_gap_upper ha hb
  linarith

/-- The bottom nonzero row of the target difference is strictly positive. -/
theorem padded_bottom_surplus {n x ε a : ℝ} (ha : |a - n * x| ≤ ε) :
    ε + 1 ≤ (paddedRow n x ε 1 : ℝ) - a := by
  have hceil := Int.le_ceil (n * x + 1 * (2 * ε + 1))
  have habs := (abs_le.mp ha).2
  dsimp [paddedRow]
  linarith

/-- Once target differences are nonnegative, their L1 norm is total surplus. -/
theorem l1_surplus_eq {ι : Type*} (s : Finset ι) (target part : ι → ℝ) (n : ℝ)
    (hrows : ∀ i ∈ s, part i ≤ target i) (hsum : ∑ i ∈ s, part i = n) :
    ∑ i ∈ s, |target i - part i| = (∑ i ∈ s, target i) - n := by
  calc
    ∑ i ∈ s, |target i - part i| = ∑ i ∈ s, (target i - part i) := by
      apply Finset.sum_congr rfl
      intro i hi
      exact abs_of_nonneg (sub_nonneg.mpr (hrows i hi))
    _ = (∑ i ∈ s, target i) - n := by rw [Finset.sum_sub_distrib, hsum]

/-- The achievability encoder/decoder error through a reference memory state.
For quantum states the metric is trace distance and the decoder is contractive. -/
theorem protocol_roundtrip_error {S T : Type*} [PseudoMetricSpace S]
    [PseudoMetricSpace T] (A : S → T) (B : T → S)
    (hB : LipschitzWith 1 B) (ρ : S) (τ : T) :
    dist (B (A ρ)) ρ ≤ dist (A ρ) τ + dist (B τ) ρ := by
  have hc : dist (B (A ρ)) (B τ) ≤ dist (A ρ) τ := by
    simpa using hB.dist_le_mul (A ρ) τ
  exact (dist_triangle (B (A ρ)) (B τ) ρ).trans (add_le_add hc le_rfl)

/-- Transfer an arbitrary compression code from the source family to the
target orbit. Contractivity is explicit, so this also applies beyond quantum
channels to any metric compression problem. -/
theorem transferred_code_error {S T M : Type*} [PseudoMetricSpace S]
    [PseudoMetricSpace T] [PseudoMetricSpace M]
    (A : S → T) (B : T → S) (E : S → M) (D : M → S)
    (hA : LipschitzWith 1 A) (hE : LipschitzWith 1 E)
    (hD : LipschitzWith 1 D) (ρ : S) (τ : T) :
    dist (A (D (E (B τ)))) τ ≤
      dist (B τ) ρ + dist (D (E ρ)) ρ + dist (A ρ) τ := by
  have hc₁ : dist (A (D (E (B τ)))) (A (D (E ρ))) ≤ dist (B τ) ρ := by
    calc
      _ ≤ dist (D (E (B τ))) (D (E ρ)) := by
        simpa using hA.dist_le_mul (D (E (B τ))) (D (E ρ))
      _ ≤ dist (E (B τ)) (E ρ) := by simpa using hD.dist_le_mul (E (B τ)) (E ρ)
      _ ≤ dist (B τ) ρ := by simpa using hE.dist_le_mul (B τ) ρ
  have hc₂ : dist (A (D (E ρ))) (A ρ) ≤ dist (D (E ρ)) ρ := by
    simpa using hA.dist_le_mul (D (E ρ)) ρ
  have ht₁ := dist_triangle (A (D (E (B τ)))) (A (D (E ρ))) τ
  have ht₂ := dist_triangle (A (D (E ρ))) (A ρ) τ
  linarith

/-- Scalar rearrangement of the averaged measurement inequality in the
irreducible-orbit memory proposition. Its quantum input is `hobs`. -/
theorem orbit_memory_scalar_bound {p₀ p₁ γ δ m h : ℝ}
    (hγ : 0 < γ) (hh : 0 < h) (hgap : p₀ - p₁ = γ)
    (hobs : p₀ - δ ≤ p₁ + γ * m / h) :
    h * (1 - δ / γ) ≤ m := by
  have he : γ - δ ≤ γ * m / h := by linarith
  have he' := (le_div_iff₀ hh).mp he
  calc
    h * (1 - δ / γ) = ((γ - δ) * h) / γ := by field_simp
    _ ≤ m := (div_le_iff₀ hγ).mpr (by nlinarith)

/-- Passing from a dimension estimate to memory measured in bits. -/
theorem memory_log_bound {m h ε γ : ℝ}
    (hh : 0 < h) (hγ : 0 < γ) (hε : ε < γ)
    (hbound : h * (1 - ε / γ) ≤ m) :
    Real.logb 2 h + Real.logb 2 (1 - ε / γ) ≤ Real.logb 2 m := by
  have hc : 0 < 1 - ε / γ := sub_pos.mpr ((div_lt_one hγ).mpr hε)
  have hp : 0 < h * (1 - ε / γ) := mul_pos hh hc
  have hlog := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2) hp hbound
  simpa only [Real.logb_mul (ne_of_gt hh) (ne_of_gt hc)] using hlog

/-- A fixed positive spectral gap makes the logarithmic error correction vanish. -/
theorem log_correction_tendsto_zero {ε : ℕ → ℝ} {γ : ℝ}
    (hε : Tendsto ε atTop (𝓝 0)) (_hγ : 0 < γ) :
    Tendsto (fun n => Real.logb 2 (1 - ε n / γ)) atTop (𝓝 0) := by
  have hc : Tendsto (fun n => 1 - ε n / γ) atTop (𝓝 (1 : ℝ)) := by
    convert tendsto_const_nhds.sub (hε.div_const γ) using 1
    simp
  simpa using hc.logb (by norm_num : (1 : ℝ) ≠ 0)

/-- The precise eventual lower-bound form of the converse, including its
additive constant. `hweyl` and `hbound` are explicit external inputs.

For every positive tolerance, eventually the memory cost exceeds `L-tolerance`;
this formulation also covers sequences whose excess cost tends to infinity.
-/
theorem optimal_memory_converse_eventually
    {memory targetDim L error : ℕ → ℝ} {γ : ℝ}
    (hγ : 0 < γ)
    (htarget : ∀ n, 0 < targetDim n)
    (herror : Tendsto error atTop (𝓝 0))
    (hweyl : Tendsto (fun n => Real.logb 2 (targetDim n) - L n) atTop (𝓝 0))
    (hbound : ∀ᶠ n in atTop, targetDim n * (1 - error n / γ) ≤ memory n) :
    ∀ η : ℝ, 0 < η →
      ∀ᶠ n in atTop, -η ≤ Real.logb 2 (memory n) - L n := by
  intro η hη
  have hsmall : ∀ᶠ n in atTop, error n < γ :=
    herror.eventually (eventually_lt_nhds hγ)
  have hcorrection := log_correction_tendsto_zero herror hγ
  have hsum : Tendsto
      (fun n => (Real.logb 2 (targetDim n) - L n) +
        Real.logb 2 (1 - error n / γ)) atTop (𝓝 (0 : ℝ)) := by
    simpa using hweyl.add hcorrection
  have hevent : ∀ᶠ n in atTop,
      -η < (Real.logb 2 (targetDim n) - L n) +
        Real.logb 2 (1 - error n / γ) :=
    hsum.eventually (eventually_gt_nhds (by linarith : -η < (0 : ℝ)))
  filter_upwards [hbound, hsmall, hevent] with n hn hsmalln heventn
  have hlog := memory_log_bound (htarget n) hγ hsmalln hn
  linarith

/-- The eventual formulation implies the manuscript's genuine extended-real
`liminf` inequality, including the possible value `+∞`. -/
theorem nonnegative_ereal_liminf_of_eventual_lower_bound {a : ℕ → ℝ}
    (ha : ∀ η : ℝ, 0 < η → ∀ᶠ n in atTop, -η ≤ a n) :
    (0 : EReal) ≤ liminf (fun n => (a n : EReal)) atTop := by
  apply (le_liminf_iff').2
  intro y hy
  obtain ⟨z, hyz, hz⟩ := EReal.lt_iff_exists_real_btwn.mp hy
  have hz' : z < 0 := by exact_mod_cast hz
  filter_upwards [ha (-z) (by linarith)] with n hn
  have hn' : z ≤ a n := by simpa using hn
  exact hyz.le.trans (EReal.coe_le_coe_iff.mpr hn')

/-- A natural-number memory/target dimension version, with the original error
and the representation-transfer error treated separately as in Theorem 1. -/
theorem optimal_memory_converse
    {memory targetDim : ℕ → ℕ} {L error transferError : ℕ → ℝ} {γ : ℝ}
    (hγ : 0 < γ)
    (htarget : ∀ n, 0 < targetDim n)
    (herror : Tendsto error atTop (𝓝 0))
    (htransfer : Tendsto transferError atTop (𝓝 0))
    (hweyl : Tendsto (fun n => Real.logb 2 (targetDim n) - L n) atTop (𝓝 0))
    (hbound : ∀ᶠ n in atTop,
      (targetDim n : ℝ) * (1 - (error n + transferError n) / γ) ≤ memory n) :
    (0 : EReal) ≤
      liminf (fun n => ((Real.logb 2 (memory n) - L n : ℝ) : EReal)) atTop := by
  apply nonnegative_ereal_liminf_of_eventual_lower_bound
  apply optimal_memory_converse_eventually hγ
    (fun n => Nat.cast_pos.mpr (htarget n))
    (by simpa using herror.add htransfer) hweyl hbound

end FreeEntropy
