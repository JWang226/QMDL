/-
Copyright (c) 2026 Free Entropy formalization contributors.
See LICENSE and NOTICE in the repository root for license and attribution.
-/

import FreeEntropy.ExteriorSupportedOffsets
import FreeEntropy.ExteriorRootCounting

/-! Rank-sensitive counting of actual root assignments and canonical weight
multiplicities. The root set and the disjoint fibers are explicitly finite. -/
noncomputable section
open scoped BigOperators
namespace FreeEntropy.ExteriorRepresentation
open CasimirWeights CartanLieCloning KostantCounting
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
variable {d : ℕ}

def rankLowerRoots (rank : ℕ) : Finset (LowerRoot d) :=
  Finset.univ.filter (fun r => r.val.2.val < rank)

def rankLowerRootEquiv (rank : ℕ) (hr : rank ≤ d) :
    {r : LowerRoot d // r ∈ rankLowerRoots rank} ≃ LowerRoot rank where
  toFun r := ⟨(⟨r.val.val.1.val, by have h := (Finset.mem_filter.mp r.property).2; have hlt := r.val.property; omega⟩,
    ⟨r.val.val.2.val, (Finset.mem_filter.mp r.property).2⟩), r.val.property⟩
  invFun r := ⟨⟨(⟨r.val.1.val, lt_of_lt_of_le r.val.1.isLt hr⟩,
    ⟨r.val.2.val, lt_of_lt_of_le r.val.2.isLt hr⟩), r.property⟩,
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, r.val.2.isLt⟩⟩
  left_inv r := by rfl
  right_inv r := by rfl

theorem card_rankLowerRoots (rank : ℕ) (hr : rank ≤ d) :
    (rankLowerRoots (d := d) rank).card = rank.choose 2 := by
  rw [← Fintype.card_coe, Fintype.card_congr (rankLowerRootEquiv rank hr), card_lowerRoot]

theorem rank_root_fibers_depth_le (rank : ℕ) (hr : rank ≤ d) (hr2 : 2 ≤ rank)
    (s : Finset (Fin (d - 1) → ℕ))
    (hs : ∀ delta ∈ s, SupportedSimpleOffset rank delta) (t : ℕ) :
    (∑ delta ∈ s with depth delta = t, (lowerWeightFiber (simpleRootAssignment delta)).card) ≤
      (t + rank.choose 2 - 1).choose (rank.choose 2 - 1) := by
  classical
  let roots := rankLowerRoots (d := d) rank
  let height := fun r : LowerRoot d => r.val.2.val - r.val.1.val
  let k : LowerRoot d := ⟨(⟨0, by omega⟩, ⟨1, by omega⟩), by change (0 : ℕ) < 1; omega⟩
  have hk : k ∈ roots := Finset.mem_filter.mpr ⟨Finset.mem_univ _, by dsimp [k]; omega⟩
  have hh : ∀ r ∈ roots, 0 < height r := fun r _ => Nat.sub_pos_of_lt r.property
  have hdj : (↑(s.filter (fun delta => depth delta = t)) : Set (Fin (d - 1) → ℕ)).PairwiseDisjoint
      (fun delta => lowerWeightFiber (simpleRootAssignment delta)) := by
    intro c hc e he hce
    apply Finset.disjoint_left.mpr
    intro a hac hae
    apply hce
    apply offset_injective
    funext j
    have hx := congrFun (((mem_lowerWeightFiber _ _).mp hac).symm.trans
      ((mem_lowerWeightFiber _ _).mp hae)) j
    have hx' := congrArg (fun z : ℤ => (z : ℝ)) hx
    dsimp only at hx'
    rw [simpleRootAssignment_shift, simpleRootAssignment_shift] at hx'
    linarith
  rw [← Finset.card_biUnion hdj]
  have hsub : (s.filter (fun delta => depth delta = t)).biUnion
      (fun delta => lowerWeightFiber (simpleRootAssignment delta)) ⊆ weightedAssignments roots height t := by
    intro a ha
    obtain ⟨delta, hdelta, hadelta⟩ := Finset.mem_biUnion.mp ha
    obtain ⟨hds, hdt⟩ := Finset.mem_filter.mp hdelta
    have hsupport : a.support ⊆ roots := by
      intro r hr
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
        lowerWeightFiber_root_support (simpleRootAssignment delta) a rank
          (simpleRootAssignment_zero_tail rank delta (hs delta hds)) hadelta r (Finsupp.mem_support_iff.mp hr)⟩
    apply (mem_weightedAssignments roots height hh t a).mpr
    refine ⟨hsupport, ?_⟩
    have he : weightedDepth roots height a = rootDepth a := by
      unfold weightedDepth rootDepth
      apply Finset.sum_subset (Finset.subset_univ _) 
      intro r _ hr
      have hz : a r = 0 := Finsupp.notMem_support_iff.mp (fun h => hr (hsupport h))
      simp [height, hz]
    rw [he, rootDepth_eq_of_weightShift_eq a (simpleRootAssignment delta)
      ((mem_lowerWeightFiber _ _).mp hadelta), simpleRootAssignment_depth, hdt]
  have hcard := (Finset.card_le_card hsub).trans (card_weightedAssignments_le roots height hh k hk t)
  simpa only [roots, card_rankLowerRoots rank hr] using hcard

/-- The actual canonical multiplicity is bounded by its actual root fiber at
all depths. Shallow equality is proved separately, with no model premise. -/
theorem canonical_offsetMultiplicity_le_rootFiber
    (mu : Fin d → ℕ) (hmu : Antitone mu) (delta : Fin (d - 1) → ℕ) :
    (canonicalWeightModel mu).offsetMultiplicity delta ≤
      (lowerWeightFiber (simpleRootAssignment delta)).card := by
  classical
  by_cases hz : (canonicalWeightModel mu).offsetMultiplicity delta = 0
  · rw [hz]; exact Nat.zero_le _
  · have hc : (Finset.univ.filter (fun a => (canonicalWeightModel mu).weight a =
        (canonicalWeightModel mu).row - offset delta)).Nonempty := by
      apply Finset.card_pos.mp
      exact Nat.pos_of_ne_zero hz
    obtain ⟨a, ha⟩ := hc
    have hw := (Finset.mem_filter.mp ha).2
    rw [canonicalWeight_spec, canonicalWeightModel_row mu hmu] at hw
    have hshift (k : Fin d) : (canonicalWeight mu a k : ℤ) - (mu k : ℤ) =
        rootWeightShift (simpleRootAssignment delta) k := by
      have hh := congrFun hw k
      have hs := simpleRootAssignment_shift delta k
      have he : (canonicalWeight mu a k : ℝ) - (mu k : ℝ) =
          (rootWeightShift (simpleRootAssignment delta) k : ℝ) := by
        dsimp at hh
        linarith
      exact_mod_cast he
    have hwt : (canonicalWeightModel mu).row - offset delta =
        fun k => (canonicalWeight mu a k : ℝ) := by
      rw [canonicalWeightModel_row mu hmu]
      exact hw.symm
    change weightMultiplicity (canonicalWeightModel mu).weight _ ≤ _
    rw [hwt]
    have hcard : weightMultiplicity (canonicalWeightModel mu).weight
        (fun k => (canonicalWeight mu a k : ℝ)) =
        Fintype.card {b : IrrepIndex mu // canonicalWeight mu b = canonicalWeight mu a} := by
      unfold weightMultiplicity
      rw [← Fintype.card_subtype]
      apply Fintype.card_congr
      apply Equiv.subtypeEquivRight
      intro b
      rw [canonicalWeight_spec]
      constructor
      · intro h; funext k; exact_mod_cast congrFun h k
      · intro h; rw [h]
    rw [hcard]
    exact canonicalWeight_card_le_rootFiber mu (canonicalWeight mu a) hmu _ hshift

theorem canonical_offsetMultiplicity_rank_depth_le
    (mu : Fin d → ℕ) (hmu : Antitone mu) (rank : ℕ) (hr : rank ≤ d) (hr2 : 2 ≤ rank)
    (s : Finset (Fin (d - 1) → ℕ)) (hs : ∀ delta ∈ s, SupportedSimpleOffset rank delta) (t : ℕ) :
    (∑ delta ∈ s with depth delta = t, (canonicalWeightModel mu).offsetMultiplicity delta) ≤
      (t + rank.choose 2 - 1).choose (rank.choose 2 - 1) :=
  (Finset.sum_le_sum (fun delta _ => canonical_offsetMultiplicity_le_rootFiber mu hmu delta)).trans
    (rank_root_fibers_depth_le rank hr hr2 s hs t)

end FreeEntropy.ExteriorRepresentation
