/-
Copyright (c) 2026 Free Entropy formalization contributors.
See LICENSE and NOTICE in the repository root for license and attribution.
-/

import FreeEntropy.CanonicalFullCloning

/-! The manuscript's single explicit constant applies at every rank,
since the mean-depth term vanishes for the rank-one spectrum. -/
noncomputable section
namespace FreeEntropy.ExteriorRepresentation
open CartanLieCloning CasimirWeights TraceDistance
set_option backward.isDefEq.respectTransparency false
variable {d r : ℕ}

theorem cloningCountRank_constant_eq (s : FixedSpectrum d r) :
    Theorem2.cloningConstant d (cloningCountRank d r) s.qx = Theorem2.cloningConstant d r s.qx := by
  by_cases hr : r = 1
  · subst r
    simp [cloningCountRank, Theorem2.cloningConstant, MeanDepth.meanDepthConstant]
  · simp [cloningCountRank, hr]

/-- The sharp stated constant is valid at every positive rank, including
zero row difference, for actual canonical CPTP maps. -/
theorem canonical_cloning_accuracy_bounds
    (s : FixedSpectrum d r) (hd : 2 ≤ d)
    (mu nu : Fin d → ℕ) (hmu : Antitone mu) (hnu : Antitone nu)
    (hinc : Antitone (fun i => (nu i : ℝ) - (mu i : ℝ)))
    (hzero : ∀ i : Fin d, r ≤ i.val → nu i = mu i)
    (D g : ℕ) (b : ℝ) (hb : 0 ≤ b) (hbg : b ≤ (g : ℝ))
    (hDnorm : l1 (fun i => (nu i : ℝ) - (mu i : ℝ)) ≤ (D : ℝ))
    (hgap : ∀ j : Fin (d - 1), j.val < r →
      (g : ℝ) ≤ (mu (left j) : ℝ) - (mu (right j) : ℝ)) :
    traceDistance ((canonicalForward mu nu hmu hnu hinc).toFun
        ((canonicalWeightModel mu).relativeState (fun j => s.adjacentRatio j.val)))
      ((canonicalWeightModel nu).relativeState (fun j => s.adjacentRatio j.val)) ≤
        Theorem2.cloningConstant d r s.qx * (D : ℝ) / (b + 1) ∧
    traceDistance ((canonicalReverse mu nu hmu hnu hinc).toFun
        ((canonicalWeightModel nu).relativeState (fun j => s.adjacentRatio j.val)))
      ((canonicalWeightModel mu).relativeState (fun j => s.adjacentRatio j.val)) ≤
        Theorem2.cloningConstant d r s.qx * (D : ℝ) / (b + 1) := by
  simpa only [cloningCountRank_constant_eq] using
    canonical_cloning_error_all_ranks s hd mu nu hmu hnu hinc hzero D g b hb hbg hDnorm hgap

/-- Only natural highest rows, their dominance, and their common spectral
support are supplied. The L1 difference and the row gap are computed. -/
theorem canonical_cloning_accuracy_rows
    (s : FixedSpectrum d r) (hd : 2 ≤ d)
    (mu nu : Fin d → ℕ) (hmu : Antitone mu) (hnu : Antitone nu)
    (hinc : Antitone (fun i => (nu i : ℝ) - (mu i : ℝ)))
    (hzero : ∀ i : Fin d, r ≤ i.val → nu i = mu i) :
    traceDistance ((canonicalForward mu nu hmu hnu hinc).toFun
        ((canonicalWeightModel mu).relativeState (fun j => s.adjacentRatio j.val)))
      ((canonicalWeightModel nu).relativeState (fun j => s.adjacentRatio j.val)) ≤
        Theorem2.cloningConstant d r s.qx * (differenceNorm mu nu : ℝ) /
          ((minimumRowGap mu r hd s.rank_pos : ℝ) + 1) ∧
    traceDistance ((canonicalReverse mu nu hmu hnu hinc).toFun
        ((canonicalWeightModel nu).relativeState (fun j => s.adjacentRatio j.val)))
      ((canonicalWeightModel mu).relativeState (fun j => s.adjacentRatio j.val)) ≤
        Theorem2.cloningConstant d r s.qx * (differenceNorm mu nu : ℝ) /
          ((minimumRowGap mu r hd s.rank_pos : ℝ) + 1) := by
  simpa only [cloningCountRank_constant_eq] using canonical_cloning_error_rows s hd mu nu hmu hnu hinc hzero

end FreeEntropy.ExteriorRepresentation
