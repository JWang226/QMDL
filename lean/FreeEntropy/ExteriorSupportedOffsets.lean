/-
Copyright (c) 2026 Free Entropy formalization contributors.
See LICENSE and NOTICE in the repository root for license and attribution.
-/

import FreeEntropy.ExteriorSimpleOffsets
import FreeEntropy.CartanMultiplicity

/-! Rank-supported exact shallow multiplicity for the actual canonical
matrix models. Only gaps below the positive rank are required. -/
noncomputable section
open scoped BigOperators
namespace FreeEntropy.ExteriorRepresentation
open CasimirWeights CartanLieCloning
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
variable {d : ℕ}

/-- No simple root at or beyond the rank boundary occurs. -/
def SupportedSimpleOffset (rank : ℕ) (delta : Fin (d - 1) → ℕ) : Prop :=
  ∀ j, rank ≤ j.val + 1 → delta j = 0

theorem supportedSimpleOffset_zero_tail (rank : ℕ) (delta : Fin (d - 1) → ℕ)
    (hdelta : SupportedSimpleOffset rank delta) (k : Fin d) (hk : rank ≤ k.val) :
    offset delta k = 0 := by
  classical
  apply Finset.sum_eq_zero
  intro j _
  by_cases hleft : k = left j
  · have hj : rank ≤ j.val + 1 := by rw [hleft] at hk; change rank ≤ j.val at hk; omega
    rw [hdelta j hj, Nat.cast_zero, zero_mul]
  · by_cases hright : k = right j
    · have hj : rank ≤ j.val + 1 := by rw [hright] at hk; exact hk
      rw [hdelta j hj, Nat.cast_zero, zero_mul]
    · simp [simpleRoot, hleft, hright]

theorem simpleRootAssignment_zero_tail (rank : ℕ) (delta : Fin (d - 1) → ℕ)
    (hdelta : SupportedSimpleOffset rank delta) (k : Fin d) (hk : rank ≤ k.val) :
    rootWeightShift (simpleRootAssignment delta) k = 0 := by
  have h := simpleRootAssignment_shift delta k
  rw [supportedSimpleOffset_zero_tail rank delta hdelta k hk, neg_zero] at h
  exact_mod_cast h

private theorem canonical_model_card_eq (mu wt : Fin d → ℕ) :
    weightMultiplicity (canonicalWeightModel mu).weight (fun k => (wt k : ℝ)) =
      Module.finrank ℂ (actualWeightSpace mu wt) := by
  classical
  rw [← canonicalWeight_card_eq_finrank]
  change (Finset.univ.filter (fun a => (canonicalWeightModel mu).weight a = _)).card = _
  rw [← Fintype.card_subtype]
  apply Fintype.card_congr
  apply Equiv.subtypeEquivRight
  intro a
  rw [canonicalWeight_spec]
  constructor
  · intro h
    funext k
    exact_mod_cast congrFun h k
  · rintro rfl
    rfl

theorem canonical_offsetMultiplicity_shallow_supported
    (mu : Fin d → ℕ) (hmu : Antitone mu) (g rank : ℕ)
    (hgap : ∀ j : Fin d, ∀ hj : j.val + 1 < d,
      j.val + 1 < rank → g + mu ⟨j.val + 1, hj⟩ ≤ mu j)
    (delta : Fin (d - 1) → ℕ) (hdelta : SupportedSimpleOffset rank delta)
    (hdepth : depth delta ≤ g) :
    (canonicalWeightModel mu).offsetMultiplicity delta =
      (lowerWeightFiber (simpleRootAssignment delta)).card := by
  classical
  let a := simpleRootAssignment delta
  have ha : rootDepth a ≤ g := by simpa only [a, simpleRootAssignment_depth] using hdepth
  obtain ⟨wt, hshift, hlo⟩ := rank_supported_lowerWeightFiber_card_le_weight_finrank mu hmu g rank hgap a ha
    (simpleRootAssignment_zero_tail rank delta hdelta)
  have hwt : (canonicalWeightModel mu).row - offset delta = fun k => (wt k : ℝ) := by
    rw [canonicalWeightModel_row mu hmu]
    funext k
    have he : (wt k : ℝ) - (mu k : ℝ) = (rootWeightShift a k : ℝ) := by exact_mod_cast hshift k
    rw [show (rootWeightShift a k : ℝ) = -offset delta k from simpleRootAssignment_shift delta k] at he
    change (mu k : ℝ) - offset delta k = (wt k : ℝ)
    linarith
  change weightMultiplicity (canonicalWeightModel mu).weight _ = _
  rw [hwt, canonical_model_card_eq]
  exact Nat.le_antisymm (actualWeight_finrank_le_rootFiber mu wt hmu a hshift) hlo

/-- Two actual canonical representations agree at each common shallow
rank-supported offset when both sets of positive-rank gaps exceed the depth. -/
theorem canonical_offsetMultiplicity_shallow_eq
    (mu nu : Fin d → ℕ) (hmu : Antitone mu) (hnu : Antitone nu) (g rank : ℕ)
    (hgapmu : ∀ j : Fin d, ∀ hj : j.val + 1 < d,
      j.val + 1 < rank → g + mu ⟨j.val + 1, hj⟩ ≤ mu j)
    (hgapnu : ∀ j : Fin d, ∀ hj : j.val + 1 < d,
      j.val + 1 < rank → g + nu ⟨j.val + 1, hj⟩ ≤ nu j)
    (delta : Fin (d - 1) → ℕ) (hdelta : SupportedSimpleOffset rank delta)
    (hdepth : depth delta ≤ g) :
    (canonicalWeightModel mu).offsetMultiplicity delta =
      (canonicalWeightModel nu).offsetMultiplicity delta := by
  rw [canonical_offsetMultiplicity_shallow_supported mu hmu g rank hgapmu delta hdelta hdepth,
    canonical_offsetMultiplicity_shallow_supported nu hnu g rank hgapnu delta hdelta hdepth]

end FreeEntropy.ExteriorRepresentation
