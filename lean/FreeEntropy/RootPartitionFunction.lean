/-
Copyright (c) 2026 Free Entropy formalization contributors.
See LICENSE and NOTICE in the repository root for license and attribution.
-/

import FreeEntropy.KostantWeightData
import FreeEntropy.SpectrumBounds
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Field.GeomSum

/-!
# Exact positive-root product bound for the partition function

A finite injective root encoding is included in a finite box of exponents.
Its monomial sum is bounded by the box sum, which factors into finite
geometric sums. Thus the exact product bound needs no infinite-series or
representation-theoretic summability assumption. Zero ratios are allowed.
-/

noncomputable section
open scoped BigOperators
open FreeEntropy.KostantCounting FreeEntropy.KostantWeightData

namespace FreeEntropy.RootPartitionFunction
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 600000

/-- A finite collection of distinct nonnegative exponent vectors has its
monomial sum bounded by the full product of geometric-series sums. -/
theorem monomial_sum_le_product {H R : Type*} [Fintype H] [Fintype R]
    [DecidableEq H] [DecidableEq R] (c : H → R → ℕ) (hinj : Function.Injective c)
    (ratio : R → ℝ) (hratio : ∀ i, 0 ≤ ratio i) (hlt : ∀ i, ratio i < 1) :
    (∑ h, ∏ i, ratio i ^ c h i) ≤ ∏ i, (1 - ratio i)⁻¹ := by
  let bound : R → ℕ := fun i => (∑ h, c h i) + 1
  have hb (h : H) (i : R) : c h i < bound i :=
    Nat.lt_succ_of_le (Finset.single_le_sum (f := fun k => c k i) (fun _ _ => Nat.zero_le _) (Finset.mem_univ h))
  let code : H → (∀ i, Fin (bound i)) := fun h i => ⟨c h i, hb h i⟩
  have hi : Function.Injective code := by
    intro h k he
    apply hinj
    funext i
    exact congrArg Fin.val (congrFun he i)
  have hs : (∑ h, ∏ i, ratio i ^ c h i) ≤
      ∑ z : ∀ i, Fin (bound i), ∏ i, ratio i ^ (z i).val := by
    have hsub : Finset.univ.image code ⊆ (Finset.univ : Finset (∀ i, Fin (bound i))) :=
      Finset.subset_univ _
    have h := Finset.sum_le_sum_of_subset_of_nonneg (f := fun z => ∏ i, ratio i ^ (z i).val) hsub (fun z _ _ =>
      Finset.prod_nonneg (fun i _ => pow_nonneg (hratio i) (z i).val))
    rw [Finset.sum_image (fun _ _ _ _ he => hi he)] at h
    exact h
  rw [← Fintype.prod_sum (fun i (j : Fin (bound i)) => ratio i ^ j.val)] at hs
  apply hs.trans
  apply Finset.prod_le_prod
  · intro i _
    exact Finset.sum_nonneg (fun k _ => pow_nonneg (hratio i) k.val)
  · intro i _
    have h := geom_sum_Ico_le_of_lt_one (m := 0) (n := bound i) (hratio i) (hlt i)
    simpa only [Fin.sum_univ_eq_sum_range, Nat.Ico_zero_eq_range, pow_zero, one_div] using h

/-- The ratio attached to a positive root is the product of its adjacent
ratios. This convention is valid even when some eigenvalues vanish. -/
def rootRatio (ratio : ℕ → ℝ) (p : ℕ × ℕ) : ℝ :=
  ∏ j ∈ Finset.Ico p.1 p.2, ratio j

theorem rootRatio_nonneg (ratio : ℕ → ℝ) (h : ∀ j, 0 ≤ ratio j) (p : ℕ × ℕ) :
    0 ≤ rootRatio ratio p := Finset.prod_nonneg (fun j _ => h j)

theorem rootRatio_lt_one (ratio : ℕ → ℝ) (h : ∀ j, 0 ≤ ratio j)
    (hlt : ∀ j, ratio j < 1) (p : ℕ × ℕ) (hp : p.1 < p.2) :
    rootRatio ratio p < 1 := by
  have hi : p.1 ∈ Finset.Ico p.1 p.2 := Finset.mem_Ico.mpr ⟨le_rfl, hp⟩
  have hb := Finset.prod_le_prod_of_subset_of_le_one (Finset.singleton_subset_iff.mpr hi)
    (fun j _ => h j) (fun j _ _ => (hlt j).le)
  simp only [Finset.prod_singleton] at hb
  exact hb.trans_lt (hlt p.1)

/-- Regrouping the simple-root monomial gives the positive-root monomial. -/
theorem rootWeight_eq_root_product (d : ℕ) (ratio : ℕ → ℝ) (c : (ℕ × ℕ) →₀ ℕ) :
    rootWeight d ratio c = ∏ p ∈ Weyl.activeRoots d d, rootRatio ratio p ^ c p := by
  unfold rootWeight typeAOffset
  simp only [← Finset.prod_pow_eq_pow_sum]
  rw [Finset.prod_comm]
  apply Finset.prod_congr rfl
  intro p hp
  have hp' := Weyl.mem_activeRoots.mp hp
  have hset : (Finset.range (d - 1)).filter (fun j => p.1 < j + 1 ∧ j + 1 ≤ p.2) =
      Finset.Ico p.1 p.2 := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
    omega
  rw [rootRatio, ← hset, Finset.prod_filter, ← Finset.prod_pow]
  apply Finset.prod_congr rfl
  intro j _
  split_ifs <;> simp

/-- A supported Finsupp root encoding inherits the precise partition-product
bound, including ratios equal to zero. -/
theorem rootWeight_sum_le_product {H : Type*} [Fintype H] [DecidableEq H]
    (d : ℕ) (encode : H → ((ℕ × ℕ) →₀ ℕ)) (hinj : Function.Injective encode)
    (hsupport : ∀ h, (encode h).support ⊆ Weyl.activeRoots d d)
    (ratio : ℕ → ℝ) (hratio : ∀ j, 0 ≤ ratio j) (hlt : ∀ j, ratio j < 1) :
    (∑ h, rootWeight d ratio (encode h)) ≤
      ∏ p ∈ Weyl.activeRoots d d, (1 - rootRatio ratio p)⁻¹ := by
  let R := {p // p ∈ Weyl.activeRoots d d}
  let c : H → R → ℕ := fun h p => encode h p.val
  have hi : Function.Injective c := by
    intro h k he
    apply hinj
    ext p
    by_cases hp : p ∈ Weyl.activeRoots d d
    · exact congrFun he ⟨p, hp⟩
    · rw [Finsupp.notMem_support_iff.mp (fun hm => hp (hsupport h hm)),
        Finsupp.notMem_support_iff.mp (fun hm => hp (hsupport k hm))]
  have h := monomial_sum_le_product c hi (fun p => rootRatio ratio p.val)
    (fun p => rootRatio_nonneg ratio hratio p.val)
    (fun p => rootRatio_lt_one ratio hratio hlt p.val (Weyl.mem_activeRoots.mp p.property).2.1)
  change (∑ h, ∏ p : ↥(Weyl.activeRoots d d), rootRatio ratio p.val ^ encode h p.val) ≤
    ∏ p : ↥(Weyl.activeRoots d d), (1 - rootRatio ratio p.val)⁻¹ at h
  have heq (f : (ℕ × ℕ) → ℝ) :
      (∏ p : ↥(Weyl.activeRoots d d), f p.val) = ∏ p ∈ Weyl.activeRoots d d, f p :=
    (Finset.prod_subtype (Weyl.activeRoots d d) (fun _ => Iff.rfl) f).symm
  have hl (b : H) : (∏ p : ↥(Weyl.activeRoots d d), rootRatio ratio p.val ^ encode b p.val) =
      rootWeight d ratio (encode b) :=
    (heq (fun p => rootRatio ratio p ^ encode b p)).trans (rootWeight_eq_root_product d ratio (encode b)).symm
  rw [heq (fun p => (1 - rootRatio ratio p)⁻¹)] at h
  simpa only [hl] using h

/-- Adjacent positive eigenvalue ratios telescope along a positive root. -/
theorem adjacentRatio_product {d r : ℕ} (s : FixedSpectrum d r) (i j : ℕ)
    (hij : i ≤ j) (hj : j < r) :
    (∏ k ∈ Finset.Ico i j, s.adjacentRatio k) = s.eigenvalue j / s.eigenvalue i := by
  induction j generalizing i with
  | zero =>
    have hi : i = 0 := by omega
    subst i
    simp [(s.positive 0 hj).ne']
  | succ j ih =>
    by_cases he : i = j + 1
    · subst i
      simp [(s.positive (j + 1) hj).ne']
    · have hij' : i ≤ j := by omega
      rw [Finset.prod_Ico_succ_top hij', ih i hij' (by omega)]
      have hadj : s.adjacentRatio j = s.eigenvalue (j + 1) / s.eigenvalue j := by
        simp [FixedSpectrum.adjacentRatio, hj]
      rw [hadj]
      field_simp [(s.positive j (by omega)).ne', (s.positive i (by omega)).ne']

/-- Roots leaving the positive rank have zero ratio, including roots lying
entirely in the padded zero-eigenvalue coordinates. -/
theorem rootRatio_zero_of_rank_le {d r : ℕ} (s : FixedSpectrum d r) (p : ℕ × ℕ)
    (hp : p.1 < p.2) (hr : r ≤ p.2) : rootRatio s.adjacentRatio p = 0 := by
  have hmem : p.2 - 1 ∈ Finset.Ico p.1 p.2 := Finset.mem_Ico.mpr (by omega)
  apply Finset.prod_eq_zero hmem
  simp only [FixedSpectrum.adjacentRatio]
  rw [if_neg (by omega)]

/-- Extra ambient roots contribute the factor one, so the exact product is
the paper's product over the nonzero eigenvalues even in deficient rank. -/
theorem root_product_eq_spectralProduct {d r : ℕ} (s : FixedSpectrum d r) :
    (∏ p ∈ Weyl.activeRoots d d, (1 - rootRatio s.adjacentRatio p)) = s.spectralProduct := by
  have hsub : Weyl.activeRoots r r ⊆ Weyl.activeRoots d d := by
    intro p hp
    obtain ⟨hi, hij, hj⟩ := Weyl.mem_activeRoots.mp hp
    exact Weyl.mem_activeRoots.mpr ⟨hi.trans_le s.rank_le, hij, hj.trans_le s.rank_le⟩
  have hprod : (∏ p ∈ Weyl.activeRoots r r, (1 - rootRatio s.adjacentRatio p)) =
      ∏ p ∈ Weyl.activeRoots d d, (1 - rootRatio s.adjacentRatio p) := by
    apply Finset.prod_subset hsub
    intro p hp hpr
    have hp' := Weyl.mem_activeRoots.mp hp
    have hj : r ≤ p.2 := by
      by_contra h
      apply hpr
      exact Weyl.mem_activeRoots.mpr ⟨by omega, hp'.2.1, by omega⟩
    rw [rootRatio_zero_of_rank_le s p hp'.2.1 hj]
    simp
  rw [← hprod, FixedSpectrum.spectralProduct]
  apply Finset.prod_congr rfl
  intro p hp
  have hp' := Weyl.mem_activeRoots.mp hp
  rw [rootRatio, adjacentRatio_product s p.1 p.2 hp'.2.1.le hp'.2.2]

/-- The exact representation-state partition bound follows from an
injective root encoding. The ambient dimension and positive rank may differ. -/
theorem fixedSpectrum_partition_upper {d r : ℕ} (s : FixedSpectrum d r)
    {H : Type*} [Fintype H] [DecidableEq H]
    (encode : H → ((ℕ × ℕ) →₀ ℕ)) (hinj : Function.Injective encode)
    (hsupport : ∀ h, (encode h).support ⊆ Weyl.activeRoots d d) :
    (∑ h, rootWeight d s.adjacentRatio (encode h)) ≤ s.spectralProduct⁻¹ := by
  have h := rootWeight_sum_le_product d encode hinj hsupport s.adjacentRatio
    s.adjacentRatio_nonneg s.adjacentRatio_lt_one
  rwa [Finset.prod_inv_distrib, root_product_eq_spectralProduct] at h

/-- The largest normalized coefficient is bounded below by the paper's
precise spectral product. Only the root encoding and an actual zero root
assignment representing the highest vector are required. -/
theorem fixedSpectrum_top_lower {d r : ℕ} (s : FixedSpectrum d r)
    {H : Type*} [Fintype H] [DecidableEq H]
    (encode : H → ((ℕ × ℕ) →₀ ℕ)) (hinj : Function.Injective encode)
    (hsupport : ∀ h, (encode h).support ⊆ Weyl.activeRoots d d)
    (highest : H) (hhighest : encode highest = 0) :
    s.spectralProduct ≤ 1 / (∑ h, rootWeight d s.adjacentRatio (encode h)) := by
  have hnonneg (h : H) : 0 ≤ rootWeight d s.adjacentRatio (encode h) :=
    rootWeight_nonneg d s.adjacentRatio (fun j _ => s.adjacentRatio_nonneg j) _
  have hZ : 0 < ∑ h, rootWeight d s.adjacentRatio (encode h) := by
    have h := Finset.single_le_sum (fun h _ => hnonneg h) (Finset.mem_univ highest)
    rw [hhighest, rootWeight_zero] at h
    exact zero_lt_one.trans_le h
  have hu := fixedSpectrum_partition_upper s encode hinj hsupport
  apply (le_div_iff₀ hZ).mpr
  have hm := mul_le_mul_of_nonneg_left hu s.spectralProduct_pos.le
  simpa only [mul_inv_cancel₀ s.spectralProduct_pos.ne'] using hm

/-- Apply the sharp partition bound directly to normalized weight data. -/
theorem weightData_top_lower {d r N : ℕ} {q : ℝ} (s : FixedSpectrum d r)
    {H : Type*} [Fintype H] [DecidableEq H] (W : GeometricOrbit.WeightData H N q)
    (encode : H → ((ℕ × ℕ) →₀ ℕ)) (hinj : Function.Injective encode)
    (hsupport : ∀ h, (encode h).support ⊆ Weyl.activeRoots d d)
    (hweight : ∀ h, W.weight h = rootWeight d s.adjacentRatio (encode h))
    (hhighest : encode W.highest = 0) : s.spectralProduct ≤ 1 / W.normalizer := by
  have hn : W.normalizer = ∑ h, rootWeight d s.adjacentRatio (encode h) := by
    simp [GeometricOrbit.WeightData.normalizer, WeightNormalization.partitionFunction, hweight]
  rw [hn]
  exact fixedSpectrum_top_lower s encode hinj hsupport W.highest hhighest

/-- The exact constant in the paper's uniform spectral-gap lemma follows
from actual root-encoded weights, including rank-deficient spectra. -/
theorem weightData_gammaX_gap {d r N : ℕ} (s : FixedSpectrum d r)
    {H : Type*} [Fintype H] [DecidableEq H] (W : GeometricOrbit.WeightData H N s.qx)
    (encode : H → ((ℕ × ℕ) →₀ ℕ)) (hinj : Function.Injective encode)
    (hsupport : ∀ h, (encode h).support ⊆ Weyl.activeRoots d d)
    (hweight : ∀ h, W.weight h = rootWeight d s.adjacentRatio (encode h))
    (hhighest : encode W.highest = 0) :
    s.gammaX ≤ 1 / W.normalizer - s.qx * (1 / W.normalizer) :=
  s.gammaX_le_eigenvalue_gap (weightData_top_lower s W encode hinj hsupport hweight hhighest) le_rfl

open Matrix MeasureTheory MeasureTheory.Measure FreeEntropy.OrbitMemory FreeEntropy.TraceDistance
open FreeEntropy.SpectralProjector FreeEntropy.Twirling
open scoped Matrix.Norms.Elementwise

/-- The actual compact-orbit memory bound with the paper's precise gammaX;
its spectral-product and gap hypotheses are discharged by root encoding. -/
theorem weightData_memory_bound_gammaX {d r N : ℕ} (s : FixedSpectrum d r)
    {H M : Type*} [Fintype H] [DecidableEq H] [Fintype M] [DecidableEq M]
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [MeasurableSpace G] [BorelSpace G]
    (μ : Measure G) [IsMulLeftInvariant μ] [IsProbabilityMeasure μ]
    (W : GeometricOrbit.WeightData H N s.qx)
    (encode : H → ((ℕ × ℕ) →₀ ℕ)) (hinj : Function.Injective encode)
    (hsupport : ∀ h, (encode h).support ⊆ Weyl.activeRoots d d)
    (hweight : ∀ h, W.weight h = rootWeight d s.adjacentRatio (encode h))
    (hhighest : encode W.highest = 0)
    (U : G →* Matrix H H ℂ) (hU : Continuous U)
    (hunitary : ∀ g, (U g)ᴴ * U g = 1)
    [Representation.IsIrreducible (matrixRepresentation U)]
    (E : Channels.MatrixChannel H M) (D : Channels.MatrixChannel M H) :
    (Fintype.card H : ℝ) * (1 -
      (∫ g, traceDistance (D.toFun (E.toFun (U g * W.state * (U g)ᴴ)))
        (U g * W.state * (U g)ᴴ) ∂μ) / s.gammaX) ≤ (Fintype.card M : ℝ) := by
  letI : Nonempty H := ⟨W.highest⟩
  exact OrbitTraceDistance.irreducible_orbit_memory_bound_gammaX s μ U hU hunitary
    E.toRealLinearMap D.toRealLinearMap E.positive D.positive E.trace_preserving D.trace_preserving
    (coordinateProjection W.highest) W.state (coordinateProjection_pos _)
    (coordinateProjection_trace _) W.state_positive
    (weightData_top_lower s W encode hinj hsupport hweight hhighest) le_rfl
    W.peak_overlap (W.spectral_upper s.qx_nonneg s.qx_lt_one.le)

end FreeEntropy.RootPartitionFunction
