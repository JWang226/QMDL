/-
Copyright (c) 2026 Free Entropy formalization contributors.
See LICENSE and NOTICE in the repository root for license and attribution.
-/

import FreeEntropy.Theorem2GT

/-! The rank-one endpoint with actual GT coefficients. The only supported
root offset is zero, so all block losses vanish and reverse cloning is exact. -/
noncomputable section
open scoped BigOperators MatrixOrder ComplexOrder
namespace FreeEntropy.Theorem2GT
open GelfandTsetlin KostantCounting WeightNormalization CloningMatrices TraceDistance

/-- Rank one has no nonzero valid simple-root offsets. -/
theorem validCuts_one_eq_zero (δ : ℕ → ℕ) (hδ : ValidCuts 1 δ) : δ = 0 := by
  funext k
  by_cases hk : k = 0
  · subst k; exact hδ.1
  · exact hδ.2 k (by omega)

theorem rank_one_support_eq_singleton (s : Finset (ℕ → ℕ))
    (hs : ∀ δ ∈ s, ValidCuts 1 δ) (hz : (0 : ℕ → ℕ) ∈ s) : s = {0} := by
  classical
  ext δ
  constructor
  · intro hδ
    exact Finset.mem_singleton.mpr (validCuts_one_eq_zero δ (hs δ hδ))
  · intro hδ
    simpa only [Finset.mem_singleton.mp hδ] using hz

theorem rank_one_coefficient (s : Finset (ℕ → ℕ)) (μ : Fin 1 → ℤ)
    (hs : ∀ δ ∈ s, ValidCuts 1 δ) (hz : (0 : ℕ → ℕ) ∈ s)
    (ratio : ℕ → ℝ) (δ : ℕ → ℕ) : gtCoefficient s μ ratio δ = 1 := by
  classical
  have hμ : Dominant μ := fun i j _ => by rw [Subsingleton.elim i j]
  rw [rank_one_support_eq_singleton s hs hz]
  simp [gtCoefficient, coefficient, partitionFunction, rootMonomial,
    gtMultiplicity_zero μ hμ]

variable {H K : Type*} [Fintype H] [DecidableEq H] [Fintype K] [DecidableEq K]

/-- Rank-one cloning with every weight-coefficient fact derived from GT
patterns. The Weyl loss can be supplied by its proved row formula. -/
theorem theorem2_rank_one_gt_of_traced_blocks
    (d D g : ℕ) (s : Finset (ℕ → ℕ)) (μ ω : Fin 1 → ℤ)
    (ratio : ℕ → ℝ) (b a : ℝ)
    (R : TraceCloning.TraceBlockRealization s
      (gtMultiplicity μ) (gtMultiplicity (μ + ω))
      (gtCoefficient s μ ratio) (gtCoefficient s (μ + ω) ratio)
      (fun δ => min 1 (2 * (offsetDepth 1 δ : ℝ) * (D : ℝ) / ((g : ℝ) + 2))) a H K)
    (hs : ∀ δ ∈ s, ValidCuts 1 δ) (hz : (0 : ℕ → ℕ) ∈ s)
    (ha : 0 ≤ a) (ha1 : a ≤ 1)
    (hdim : 1 - a ≤ (d.choose 2 : ℝ) * (D : ℝ) / (b + 1)) :
    traceDistance (R.forward.toFun (mixture s (gtCoefficient s μ ratio) R.Pμ))
        (mixture s (gtCoefficient s (μ + ω) ratio) R.Pν) ≤
        Theorem2.cloningConstant d 1 0 * (D : ℝ) / (b + 1) ∧
    traceDistance (R.reverse.toFun (mixture s (gtCoefficient s (μ + ω) ratio) R.Pν))
        (mixture s (gtCoefficient s μ ratio) R.Pμ) = 0 := by
  have hc := rank_one_coefficient s μ hs hz ratio
  have hc' := rank_one_coefficient s (μ + ω) hs hz ratio
  obtain ⟨hf, hr⟩ := R.error_comparisons (Z := 1)
    (fun δ _ => by rw [hc]; norm_num) (fun δ _ => by rw [hc']; norm_num)
    ha ha1 (by norm_num) le_rfl (fun δ _ => by rw [hc, hc']; ring)
  have he (δ : ℕ → ℕ) (hδ : δ ∈ s) :
      min 1 (2 * (offsetDepth 1 δ : ℝ) * (D : ℝ) / ((g : ℝ) + 2)) = 0 := by
    rw [validCuts_one_eq_zero δ (hs δ hδ)]
    simp [offsetDepth]
  have hsum (f : (ℕ → ℕ) → ℝ) :
      (∑ δ ∈ s, min 1 (2 * (offsetDepth 1 δ : ℝ) * (D : ℝ) / ((g : ℝ) + 2)) * f δ) = 0 :=
    Finset.sum_eq_zero (fun δ hδ => by rw [he δ hδ, zero_mul])
  rw [hsum, add_zero] at hf
  rw [hsum] at hr
  constructor
  · simpa [Theorem2.cloningConstant, MeanDepth.meanDepthConstant] using hf.trans hdim
  · exact le_antisymm (by simpa using hr) (traceDistance_nonneg _ _)

/-- Rank-one integer-row form, with the Weyl dimension loss also proved. -/
theorem theorem2_rank_one_gt_from_integer_rows
    (d g : ℕ) (s : Finset (ℕ → ℕ)) (μ ω : ℕ → ℤ)
    (ratio : ℕ → ℝ) (b : ℝ)
    (R : TraceCloning.TraceBlockRealization s
      (gtMultiplicity (rankRow 1 μ)) (gtMultiplicity (rankRow 1 μ + rankRow 1 ω))
      (gtCoefficient s (rankRow 1 μ) ratio)
      (gtCoefficient s (rankRow 1 μ + rankRow 1 ω) ratio)
      (fun δ => min 1 (2 * (offsetDepth 1 δ : ℝ) * (rowDistance d ω : ℝ) /
        ((g : ℝ) + 2))) (weylRatio d μ ω) H K)
    (hμ : ∀ i j, i < j → j < d → μ j ≤ μ i)
    (hω : ∀ i j, i < j → j < d → ω j ≤ ω i)
    (hzero : ∀ i, 1 ≤ i → i < d → ω i = 0)
    (hs : ∀ δ ∈ s, ValidCuts 1 δ) (hz : (0 : ℕ → ℕ) ∈ s)
    (hb : 0 ≤ b) (hactive : ∀ i, i < 1 → i + 1 < d → b ≤ (μ i : ℝ) - (μ (i + 1) : ℝ)) :
    traceDistance (R.forward.toFun (mixture s (gtCoefficient s (rankRow 1 μ) ratio) R.Pμ))
        (mixture s (gtCoefficient s (rankRow 1 μ + rankRow 1 ω) ratio) R.Pν) ≤
        Theorem2.cloningConstant d 1 0 * (rowDistance d ω : ℝ) / (b + 1) ∧
    traceDistance (R.reverse.toFun
        (mixture s (gtCoefficient s (rankRow 1 μ + rankRow 1 ω) ratio) R.Pν))
        (mixture s (gtCoefficient s (rankRow 1 μ) ratio) R.Pμ) = 0 := by
  have hμr : ∀ i j, i < j → j < d → (μ j : ℝ) ≤ (μ i : ℝ) := by
    intro i j hij hj; exact_mod_cast hμ i j hij hj
  have hωr : ∀ i j, i < j → j < d → (ω j : ℝ) ≤ (ω i : ℝ) := by
    intro i j hij hj; exact_mod_cast hω i j hij hj
  have hzr : ∀ i, 1 ≤ i → i < d → (ω i : ℝ) = 0 := by
    intro i hi hid; rw [hzero i hi hid, Int.cast_zero]
  obtain ⟨ha, ha1⟩ := Weyl.weyl_ratio_pos_le_one_from_rows d
    (fun i => (μ i : ℝ)) (fun i => (ω i : ℝ)) hμr hωr
  have hdim := Weyl.weyl_ratio_deficit_from_rows d 1
    (fun i => (μ i : ℝ)) (fun i => (ω i : ℝ)) b hb hμr hωr hzr hactive
  rw [← rowDistance_cast] at hdim
  exact theorem2_rank_one_gt_of_traced_blocks d (rowDistance d ω) g s
    (rankRow 1 μ) (rankRow 1 ω) ratio b (weylRatio d μ ω) R hs hz ha.le ha1 hdim

end FreeEntropy.Theorem2GT
