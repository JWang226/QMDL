/-
Copyright (c) 2026 Free Entropy formalization contributors.
See LICENSE and NOTICE in the repository root for license and attribution.
-/

import FreeEntropy.CanonicalCloning

/-! A universal ambient-root constant for the actual canonical cloning maps.
This version includes rank one without invoking a binomial coefficient with
zero positive roots. The sharper rank constant is available for rank ≥ 2. -/
noncomputable section
open Matrix
open scoped BigOperators
namespace FreeEntropy.ExteriorRepresentation
open CartanLieCloning CasimirWeights WeightSectors CloningMatrices TraceDistance
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
variable {d r : ℕ}
local instance (mu : Fin d → ℕ) : Nonempty (IrrepIndex mu) :=
  Fin.pos_iff_nonempty.mp (irrep_dimension_pos mu)

/-- The ambient-root version is valid for every positive spectral rank. -/
theorem canonical_cloning_error_ambient_of_auxiliary
    (s : FixedSpectrum d r) (hd2 : 2 ≤ d)
    (mu nu : Fin d → ℕ) (hmu : Antitone mu) (hnu : Antitone nu)
    {B : Type*} [Fintype B] [DecidableEq B] [Nonempty B]
    (N : CyclicWeightModel d B)
    (hrow : (canonicalWeightModel nu).row = (canonicalWeightModel mu).row + N.row)
    (hinc : Antitone (fun i => (nu i : ℝ) - (mu i : ℝ)))
    (hzero : ∀ i : Fin d, r ≤ i.val → nu i = mu i)
    (D g : ℕ) (b : ℝ) (hD : 1 ≤ D) (hb : 0 ≤ b) (hbg : b ≤ (g : ℝ))
    (hDnorm : l1 (fun i => (nu i : ℝ) - (mu i : ℝ)) ≤ (D : ℝ))
    (hgap : ∀ j : Fin (d - 1), j.val < r →
      (g : ℝ) ≤ (mu (left j) : ℝ) - (mu (right j) : ℝ)) :
    traceDistance
      ((specifiedForward (canonicalWeightModel mu) N (canonicalWeightModel nu) hrow).toFun
        ((canonicalWeightModel mu).relativeState (fun j => s.adjacentRatio j.val)))
      ((canonicalWeightModel nu).relativeState (fun j => s.adjacentRatio j.val)) ≤
        Theorem2.cloningConstant d d s.qx * (D : ℝ) / (b + 1) ∧
    traceDistance
      ((specifiedReverse (canonicalWeightModel mu) N (canonicalWeightModel nu) hrow).toFun
        ((canonicalWeightModel nu).relativeState (fun j => s.adjacentRatio j.val)))
      ((canonicalWeightModel mu).relativeState (fun j => s.adjacentRatio j.val)) ≤
        Theorem2.cloningConstant d d s.qx * (D : ℝ) / (b + 1) := by
  classical
  have hd : 0 < d := lt_of_lt_of_le s.rank_pos s.rank_le
  let M := canonicalWeightModel mu
  let S := canonicalWeightModel nu
  let ratio := fun j : Fin (d - 1) => s.adjacentRatio j.val
  let ss := M.offsetSupport ∪ S.offsetSupport
  let offsets := ss.filter (SupportedSimpleOffset r)
  let pμ := M.relativeCoefficient ratio
  let pν := S.relativeCoefficient ratio
  have hsM : M.offsetSupport ⊆ ss := Finset.subset_union_left
  have hsS : S.offsetSupport ⊆ ss := Finset.subset_union_right
  have hs : ∀ delta ∈ offsets, SupportedSimpleOffset r delta :=
    fun _ h => (Finset.mem_filter.mp h).2
  have hratio : ∀ j, 0 ≤ ratio j := fun j => s.adjacentRatio_nonneg j.val
  have hratioq : ∀ j, ratio j ≤ s.qx := fun j => GTOrbit.adjacentRatio_le_qx s j.val
  have hrzero : ∀ j : Fin (d - 1), r ≤ j.val + 1 → ratio j = 0 := by
    intro j hj
    simp only [ratio, FixedSpectrum.adjacentRatio, if_neg (by omega : ¬j.val + 1 < r)]
  have hstateM := M.supported_mixture_eq_relativeState ratio r hrzero ss hsM
  have hstateS := S.supported_mixture_eq_relativeState ratio r hrzero ss hsS
  have hnormM : (mixture offsets pμ (fun delta => weightProjector M.weight (M.row - offset delta))).trace = 1 := by
    rw [hstateM]
    exact M.relativeState_trace ratio hratio
  have hnormS : (mixture offsets pν (fun delta => weightProjector S.weight (M.row + N.row - offset delta))).trace = 1 := by
    rw [← hrow, hstateS]
    exact S.relativeState_trace ratio hratio
  have hNrow : N.row = fun i => (nu i : ℝ) - (mu i : ℝ) := by
    funext i
    have h := congrFun hrow i
    simp only [canonicalWeightModel_row mu hmu, canonicalWeightModel_row nu hnu, Pi.add_apply] at h
    linarith
  have hgapnu (j : Fin (d - 1)) (hj : j.val < r) :
      (g : ℝ) ≤ (nu (left j) : ℝ) - (nu (right j) : ℝ) := by
    have h := hinc (show left j ≤ right j from by change j.val ≤ j.val + 1; omega)
    linarith [hgap j hj]
  have hgm : ∀ j : Fin d, ∀ hj : j.val + 1 < d, j.val + 1 < r → g + mu ⟨j.val + 1, hj⟩ ≤ mu j := by
    intro j hj hjr
    have he := hgap (⟨j.val, by omega⟩ : Fin (d - 1)) (by change j.val < r; omega)
    change (g : ℝ) ≤ (mu j : ℝ) - (mu ⟨j.val + 1, hj⟩ : ℝ) at he
    exact_mod_cast (by linarith : (g : ℝ) + (mu ⟨j.val + 1, hj⟩ : ℝ) ≤ (mu j : ℝ))
  have hgn : ∀ j : Fin d, ∀ hj : j.val + 1 < d, j.val + 1 < r → g + nu ⟨j.val + 1, hj⟩ ≤ nu j := by
    intro j hj hjr
    have he := hgapnu (⟨j.val, by omega⟩ : Fin (d - 1)) (by change j.val < r; omega)
    change (g : ℝ) ≤ (nu j : ℝ) - (nu ⟨j.val + 1, hj⟩ : ℝ) at he
    exact_mod_cast (by linarith : (g : ℝ) + (nu ⟨j.val + 1, hj⟩ : ℝ) ≤ (nu j : ℝ))
  have hshallow : ∀ delta ∈ offsets, depth delta ≤ g →
      weightMultiplicity M.weight (M.row - offset delta) =
      weightMultiplicity S.weight (M.row + N.row - offset delta) := by
    intro delta hd hsmall
    rw [← hrow]
    exact canonical_offsetMultiplicity_shallow_eq mu nu hmu hnu g r hgm hgn delta (hs delta hd) hsmall
  let R := ofSpecifiedCyclicWeights M N S hrow offsets id pμ pν D g hD
    (by rw [hNrow]; exact hDnorm)
    (fun delta _ => M.relativeCoefficient_nonneg ratio hratio delta)
    (fun delta _ => S.relativeCoefficient_nonneg ratio hratio delta) hnormM hnormS hshallow
    (by
      intro delta hd _ j hj
      have hjr : j.val < r := by
        by_contra hn
        exact hj (hs delta hd j (by omega))
      rw [← hrow, canonicalWeightModel_row nu hnu]
      exact hgapnu j hjr)
  have hdim := canonical_dimensionRatio_pos_le_one mu nu hmu hnu hd hinc
  have hmn : ∀ delta ∈ offsets,
      weightMultiplicity M.weight (M.row - offset delta) ≤
      weightMultiplicity S.weight (M.row + N.row - offset delta) := by
    intro delta _
    have h := weight_multiplicity_add_le M N S hrow (M.row - offset delta)
    have he : (M.row - offset delta) + N.row = M.row + N.row - offset delta := by abel
    simpa only [he, Fintype.card_subtype, weightMultiplicity] using h
  have he := TraceCloning.theorem2_of_traced_blocks offsets depth
    (fun delta => weightMultiplicity M.weight (M.row - offset delta))
    (fun delta => weightMultiplicity S.weight (M.row + N.row - offset delta))
    pμ pν d d D g b s.qx
    ((Fintype.card (IrrepIndex mu) : ℝ) / (Fintype.card (IrrepIndex nu) : ℝ))
    (M.relativeNormalizer ratio / S.relativeNormalizer ratio) R hd2 s.qx_nonneg s.qx_lt_one hb hbg
    hdim.1.le hdim.2
    (fun delta _ => M.relativeCoefficient_nonneg ratio hratio delta)
    (fun delta _ => S.relativeCoefficient_nonneg ratio hratio delta)
    hmn hshallow (by intro hz; omega)
    (fun delta _ => relativeCoefficient_ratio M S ratio hratio delta)
    (fun delta _ => M.relativeCoefficient_envelope ratio s.qx hratio hratioq delta)
    (fun delta _ => S.relativeCoefficient_envelope ratio s.qx hratio hratioq delta)
    (M.offsetMultiplicity_depth_le hd2 offsets)
    (by
      intro t
      rw [← hrow]
      exact S.offsetMultiplicity_depth_le hd2 offsets t)
    (canonical_dimensionRatio_deficit mu nu hmu hnu hd r b D hb hinc hzero
      (fun j hj => hbg.trans (hgap j hj)) hDnorm)
  change traceDistance ((specifiedForward M N S hrow).toFun
      (mixture offsets pμ (fun delta => weightProjector M.weight (M.row - offset delta))))
      (mixture offsets pν (fun delta => weightProjector S.weight (M.row + N.row - offset delta))) ≤ _ ∧
    traceDistance ((specifiedReverse M N S hrow).toFun
      (mixture offsets pν (fun delta => weightProjector S.weight (M.row + N.row - offset delta))))
      (mixture offsets pμ (fun delta => weightProjector M.weight (M.row - offset delta))) ≤ _ at he
  rw [← hrow, hstateM, hstateS] at he
  exact he

end FreeEntropy.ExteriorRepresentation
