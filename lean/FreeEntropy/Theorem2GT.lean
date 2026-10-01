/-
Copyright (c) 2026 Free Entropy formalization contributors.
See LICENSE and NOTICE in the repository root for license and attribution.
-/

import FreeEntropy.GTPartitions
import FreeEntropy.WeightNormalization
import FreeEntropy.TraceCloning

/-!
# Theorem 2 with the GT multiplicity and weight estimates discharged

The multiplicities are actual finite counts of rank-`r` GT patterns, and the
coefficients are actual normalized monomials in adjacent eigenvalue ratios.
Their monotonicity, shallow equality, coefficient envelopes, and partition
count bounds are proved rather than assumed. The ambient matrix spaces
remain independent of `r`: for rank-deficient states the identification of
supported GL(d) weight spaces with the GL(r) GT counts is a representation
theorem, not an identification of their full Hilbert-space dimensions.
-/

noncomputable section
open scoped BigOperators MatrixOrder ComplexOrder

namespace FreeEntropy.Theorem2GT

open GelfandTsetlin KostantCounting WeightNormalization
open CloningMatrices TraceDistance

/-- The actual GT count at a nonnegative simple-root offset. -/
def gtMultiplicity {r : ℕ} (μ : Fin r → ℤ) (δ : ℕ → ℕ) : ℕ :=
  GelfandTsetlin.multiplicity μ (coordinateOffset r δ)

theorem gtMultiplicity_zero {r : ℕ} (μ : Fin r → ℤ) (hμ : Dominant μ) :
    gtMultiplicity μ 0 = 1 := by
  have hv : ValidCuts r 0 := ⟨rfl, fun _ _ => rfl⟩
  have hcoord : coordinateOffset r 0 = 0 := by ext i; simp [coordinateOffset]
  let P₀ : OffsetPatterns μ (coordinateOffset r 0) :=
    ⟨highestPattern μ hμ, by rw [weight_highestPattern, hcoord, sub_zero]⟩
  apply Fintype.card_eq_one_iff.mpr
  refine ⟨P₀, ?_⟩
  intro P
  apply Subtype.ext
  apply drops_injective
  change drops P.val = drops (highestPattern μ hμ)
  rw [drops_highestPattern]
  have hc := (cut_eq_iff_weight_eq P.val hv).mpr P.property
  apply (weightedDepth_eq_zero_iff (Weyl.activeRoots r r)
    (fun p => p.2 - p.1)
    (fun p hp => Nat.sub_pos_of_lt (Weyl.mem_activeRoots.mp hp).2.1)
    (drops P.val) (drops_support P.val)).mp
  rw [← offsetDepth_typeAOffset, hc]
  simp [offsetDepth]

/-- The relative eigenvalue monomial for the simple-root offset. -/
def rootMonomial (r : ℕ) (ratio : ℕ → ℝ) (δ : ℕ → ℕ) : ℝ :=
  ∏ j ∈ Finset.range (r - 1), ratio j ^ δ (j + 1)

@[simp] theorem rootMonomial_zero (r : ℕ) (ratio : ℕ → ℝ) :
    rootMonomial r ratio 0 = 1 := by simp [rootMonomial]

theorem rootMonomial_nonneg (r : ℕ) (ratio : ℕ → ℝ)
    (hratio : ∀ j < r - 1, 0 ≤ ratio j) (δ : ℕ → ℕ) :
    0 ≤ rootMonomial r ratio δ :=
  Finset.prod_nonneg (fun j hj => pow_nonneg (hratio j (Finset.mem_range.mp hj)) _)

theorem sum_cuts_eq_depth (r : ℕ) (hr : 0 < r) (δ : ℕ → ℕ)
    (hδ : ValidCuts r δ) :
    (∑ j ∈ Finset.range (r - 1), δ (j + 1)) = offsetDepth r δ := by
  unfold offsetDepth
  rw [Finset.sum_range_succ, hδ.2 r le_rfl, Nat.add_zero]
  have hr' : r - 1 + 1 = r := by omega
  have hs := Finset.sum_range_succ' δ (r - 1)
  rw [hr', hδ.1, Nat.add_zero] at hs
  exact hs.symm

theorem rootMonomial_le_depth (r : ℕ) (hr : 0 < r) (ratio : ℕ → ℝ) (q : ℝ)
    (hratio : ∀ j < r - 1, 0 ≤ ratio j)
    (hbound : ∀ j < r - 1, ratio j ≤ q)
    (δ : ℕ → ℕ) (hδ : ValidCuts r δ) :
    rootMonomial r ratio δ ≤ q ^ offsetDepth r δ := by
  have h := MeanDepth.root_monomial_le (Finset.range (r - 1))
    (fun j => δ (j + 1)) ratio q
    (fun j hj => hratio j (Finset.mem_range.mp hj))
    (fun j hj => hbound j (Finset.mem_range.mp hj))
  simpa only [rootMonomial, sum_cuts_eq_depth r hr δ hδ] using h

/-- Normalized coefficients with the actual GT multiplicities in the partition function. -/
def gtCoefficient {r : ℕ} (s : Finset (ℕ → ℕ)) (μ : Fin r → ℤ)
    (ratio : ℕ → ℝ) : (ℕ → ℕ) → ℝ :=
  coefficient s (gtMultiplicity μ) (rootMonomial r ratio)

theorem normalizer_ge_one {r : ℕ} (s : Finset (ℕ → ℕ)) (μ : Fin r → ℤ)
    (hμ : Dominant μ) (hz : (0 : ℕ → ℕ) ∈ s) (ratio : ℕ → ℝ)
    (hratio : ∀ j < r - 1, 0 ≤ ratio j) :
    1 ≤ partitionFunction s (gtMultiplicity μ) (rootMonomial r ratio) :=
  partitionFunction_ge_one s _ _ (fun δ _ => rootMonomial_nonneg r ratio hratio δ)
    0 hz (gtMultiplicity_zero μ hμ) (rootMonomial_zero r ratio)

variable {H K : Type*} [Fintype H] [DecidableEq H] [Fintype K] [DecidableEq K]

/-- Theorem 2 for actual channel outputs, with every scalar weight and
multiplicity input proved from integer GT patterns and root monomials.

The remaining inputs are the concrete traced block realization and the
Weyl dimension loss. `D=0 → ω=0` expresses the meaning of the row distance;
it is not an assumption about errors or multiplicities.
-/
theorem theorem2_gt_of_traced_blocks
    (d r D g : ℕ) (s : Finset (ℕ → ℕ)) (μ ω : Fin r → ℤ)
    (ratio : ℕ → ℝ) (b q a : ℝ)
    (R : TraceCloning.TraceBlockRealization s
      (gtMultiplicity μ) (gtMultiplicity (μ + ω))
      (gtCoefficient s μ ratio) (gtCoefficient s (μ + ω) ratio)
      (fun δ => min 1 (2 * (offsetDepth r δ : ℝ) * (D : ℝ) / ((g : ℝ) + 2))) a H K)
    (hrank : 2 ≤ r) (hμ : Dominant μ) (hω : Dominant ω)
    (hs : ∀ δ ∈ s, ValidCuts r δ) (hz : (0 : ℕ → ℕ) ∈ s)
    (hratio : ∀ j < r - 1, 0 ≤ ratio j) (hbound : ∀ j < r - 1, ratio j ≤ q)
    (hq : 0 ≤ q) (hq1 : q < 1)
    (hb : 0 ≤ b) (hbg : b ≤ (g : ℝ)) (hgap : HasGap μ g)
    (hDzero : D = 0 → ω = 0) (ha : 0 ≤ a) (ha1 : a ≤ 1)
    (hdim : 1 - a ≤ (d.choose 2 : ℝ) * (D : ℝ) / (b + 1)) :
    traceDistance (R.forward.toFun (mixture s (gtCoefficient s μ ratio) R.Pμ))
        (mixture s (gtCoefficient s (μ + ω) ratio) R.Pν) ≤
        Theorem2.cloningConstant d r q * (D : ℝ) / (b + 1) ∧
    traceDistance (R.reverse.toFun (mixture s (gtCoefficient s (μ + ω) ratio) R.Pν))
        (mixture s (gtCoefficient s μ ratio) R.Pμ) ≤
        Theorem2.cloningConstant d r q * (D : ℝ) / (b + 1) := by
  classical
  have hν : Dominant (μ + ω) := fun _ _ hij => add_le_add (hμ hij) (hω hij)
  have hZm := normalizer_ge_one s μ hμ hz ratio hratio
  have hZn := normalizer_ge_one s (μ + ω) hν hz ratio hratio
  have hZmpos : 0 < partitionFunction s (gtMultiplicity μ) (rootMonomial r ratio) := by linarith
  have hZnpos : 0 < partitionFunction s (gtMultiplicity (μ + ω)) (rootMonomial r ratio) := by
    linarith
  have hw : ∀ δ ∈ s, 0 ≤ rootMonomial r ratio δ :=
    fun δ _ => rootMonomial_nonneg r ratio hratio δ
  have he : ∀ δ ∈ s, rootMonomial r ratio δ ≤ q ^ offsetDepth r δ :=
    fun δ hδ => rootMonomial_le_depth r (by omega) ratio q hratio hbound δ (hs δ hδ)
  apply TraceCloning.theorem2_of_traced_blocks s (offsetDepth r)
    (gtMultiplicity μ) (gtMultiplicity (μ + ω))
    (gtCoefficient s μ ratio) (gtCoefficient s (μ + ω) ratio) d r D g b q a
    (partitionFunction s (gtMultiplicity μ) (rootMonomial r ratio) /
      partitionFunction s (gtMultiplicity (μ + ω)) (rootMonomial r ratio)) R
    hrank hq hq1 hb hbg ha ha1
  · exact coefficient_nonneg s _ _ hw hZmpos
  · exact coefficient_nonneg s _ _ hw hZnpos
  · intro δ _
    exact multiplicity_mono hω (coordinateOffset r δ)
  · intro δ hδ hdepth
    exact multiplicity_eq_add_of_shallow δ (hs δ hδ) hω hgap hdepth
  · intro hD δ _
    simp [gtMultiplicity, hDzero hD]
  · intro δ _
    exact coefficient_ratio s _ _ _ hZmpos.ne' δ
  · exact coefficient_le_geometric s _ (offsetDepth r) _ q hw hZm he
  · exact coefficient_le_geometric s _ (offsetDepth r) _ q hw hZn he
  · exact sum_multiplicities_at_depth_le r hrank s _
      (fun δ hδ => multiplicity_le_kostantCount μ δ (hs δ hδ))
  · exact sum_multiplicities_at_depth_le r hrank s _
      (fun δ hδ => multiplicity_le_kostantCount (μ + ω) δ (hs δ hδ))
  · exact hdim

/-- Restrict an ambient integer highest weight to its first `r` rows. -/
def rankRow (r : ℕ) (μ : ℕ → ℤ) : Fin r → ℤ := fun i => μ i.val

/-- The actual integer L1 distance between the two highest weights. -/
def rowDistance (d : ℕ) (ω : ℕ → ℤ) : ℕ := ∑ i ∈ Finset.range d, (ω i).natAbs

theorem rowDistance_cast (d : ℕ) (ω : ℕ → ℤ) :
    (rowDistance d ω : ℝ) = Weyl.rowL1 d (fun i => (ω i : ℝ)) := by
  simp [rowDistance, Weyl.rowL1, Nat.cast_sum, Nat.cast_natAbs, Int.cast_abs]

/-- The full ambient Weyl product ratio; the supported multiplicities still use rank `r`. -/
def weylRatio (d : ℕ) (μ ω : ℕ → ℤ) : ℝ :=
  Weyl.activeProduct d d (fun i => (μ i : ℝ)) /
    Weyl.activeProduct d d (fun i => (μ i : ℝ) + (ω i : ℝ))

theorem rankRow_dominant {d r : ℕ} (hrd : r ≤ d) (μ : ℕ → ℤ)
    (hμ : ∀ i j, i < j → j < d → μ j ≤ μ i) : Dominant (rankRow r μ) := by
  intro i j hij
  rcases lt_or_eq_of_le hij with hij | hij
  · exact hμ i.val j.val hij (lt_of_lt_of_le j.isLt hrd)
  · rw [hij]

/-- Theorem 2 with all scalar combinatorics, normalization, and Weyl estimates
derived from actual integral rows. The remaining input is the concrete
representation-to-traced-block realization for the explicit coefficients.
-/
theorem theorem2_gt_from_integer_rows
    (d r g : ℕ) (s : Finset (ℕ → ℕ)) (μ ω : ℕ → ℤ)
    (ratio : ℕ → ℝ) (b q : ℝ)
    (R : TraceCloning.TraceBlockRealization s
      (gtMultiplicity (rankRow r μ)) (gtMultiplicity (rankRow r μ + rankRow r ω))
      (gtCoefficient s (rankRow r μ) ratio)
      (gtCoefficient s (rankRow r μ + rankRow r ω) ratio)
      (fun δ => min 1 (2 * (offsetDepth r δ : ℝ) * (rowDistance d ω : ℝ) /
        ((g : ℝ) + 2))) (weylRatio d μ ω) H K)
    (hrank : 2 ≤ r) (hrd : r ≤ d)
    (hμ : ∀ i j, i < j → j < d → μ j ≤ μ i)
    (hω : ∀ i j, i < j → j < d → ω j ≤ ω i)
    (hzero : ∀ i, r ≤ i → i < d → ω i = 0)
    (hs : ∀ δ ∈ s, ValidCuts r δ) (hz : (0 : ℕ → ℕ) ∈ s)
    (hratio : ∀ j < r - 1, 0 ≤ ratio j) (hbound : ∀ j < r - 1, ratio j ≤ q)
    (hq : 0 ≤ q) (hq1 : q < 1) (hb : 0 ≤ b) (hbg : b ≤ (g : ℝ))
    (hgap : HasGap (rankRow r μ) g)
    (hactive : ∀ i, i < r → i + 1 < d → b ≤ (μ i : ℝ) - (μ (i + 1) : ℝ)) :
    traceDistance (R.forward.toFun (mixture s (gtCoefficient s (rankRow r μ) ratio) R.Pμ))
        (mixture s (gtCoefficient s (rankRow r μ + rankRow r ω) ratio) R.Pν) ≤
        Theorem2.cloningConstant d r q * (rowDistance d ω : ℝ) / (b + 1) ∧
    traceDistance
        (R.reverse.toFun (mixture s (gtCoefficient s (rankRow r μ + rankRow r ω) ratio) R.Pν))
        (mixture s (gtCoefficient s (rankRow r μ) ratio) R.Pμ) ≤
        Theorem2.cloningConstant d r q * (rowDistance d ω : ℝ) / (b + 1) := by
  have hμreal : ∀ i j, i < j → j < d → (μ j : ℝ) ≤ (μ i : ℝ) := by
    intro i j hij hj
    exact_mod_cast hμ i j hij hj
  have hωreal : ∀ i j, i < j → j < d → (ω j : ℝ) ≤ (ω i : ℝ) := by
    intro i j hij hj
    exact_mod_cast hω i j hij hj
  have hzeroReal : ∀ i, r ≤ i → i < d → (ω i : ℝ) = 0 := by
    intro i hi hid
    rw [hzero i hi hid, Int.cast_zero]
  obtain ⟨ha, ha1⟩ := Weyl.weyl_ratio_pos_le_one_from_rows d
    (fun i => (μ i : ℝ)) (fun i => (ω i : ℝ)) hμreal hωreal
  have hdim := Weyl.weyl_ratio_deficit_from_rows d r
    (fun i => (μ i : ℝ)) (fun i => (ω i : ℝ)) b hb hμreal hωreal hzeroReal hactive
  rw [← rowDistance_cast] at hdim
  have hDzero : rowDistance d ω = 0 → rankRow r ω = 0 := by
    intro hD
    have hL1 : Weyl.rowL1 d (fun i => (ω i : ℝ)) = 0 := by
      rw [← rowDistance_cast, hD, Nat.cast_zero]
    have hzω := (Weyl.rowL1_eq_zero_iff d (fun i => (ω i : ℝ))).mp hL1
    funext i
    have hi := hzω i.val (lt_of_lt_of_le i.isLt hrd)
    exact_mod_cast hi
  exact theorem2_gt_of_traced_blocks d r (rowDistance d ω) g s
    (rankRow r μ) (rankRow r ω) ratio b q (weylRatio d μ ω) R
    hrank (rankRow_dominant hrd μ hμ) (rankRow_dominant hrd ω hω)
    hs hz hratio hbound hq hq1 hb hbg hgap hDzero ha.le ha1 hdim

end FreeEntropy.Theorem2GT
