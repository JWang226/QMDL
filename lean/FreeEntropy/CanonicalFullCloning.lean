/-
Copyright (c) 2026 Free Entropy formalization contributors.
See LICENSE and NOTICE in the repository root for license and attribution.
-/

import FreeEntropy.CanonicalAmbientCloning
import FreeEntropy.IdentityCloning

/-! Row-only canonical cloning, including zero differences and rank one.
The channels are fixed by the two actual representations. Every error
parameter is either explicit or computed directly from their natural rows. -/
noncomputable section
open Matrix
open scoped BigOperators
namespace FreeEntropy.ExteriorRepresentation
open CartanLieCloning CasimirWeights TraceDistance
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
variable {d r : ℕ}
local instance (mu : Fin d → ℕ) : Nonempty (IrrepIndex mu) :=
  Fin.pos_iff_nonempty.mp (irrep_dimension_pos mu)

/-- The sharper positive-rank count is used for rank at least two. Rank one
uses the always valid ambient-root constant. -/
def cloningCountRank (d r : ℕ) : ℕ := if r = 1 then d else r

def canonicalForward (mu nu : Fin d → ℕ) (hmu : Antitone mu) (hnu : Antitone nu)
    (hinc : Antitone (fun i => (nu i : ℝ) - (mu i : ℝ))) :
    Channels.MatrixChannel (IrrepIndex mu) (IrrepIndex nu) := by
  classical
  exact if h : nu = mu then (by subst nu; exact TraceCloning.identityChannel)
    else canonicalCartanForward mu nu hmu hnu hinc

def canonicalReverse (mu nu : Fin d → ℕ) (hmu : Antitone mu) (hnu : Antitone nu)
    (hinc : Antitone (fun i => (nu i : ℝ) - (mu i : ℝ))) :
    Channels.MatrixChannel (IrrepIndex nu) (IrrepIndex mu) := by
  classical
  exact if h : nu = mu then (by subst nu; exact TraceCloning.identityChannel)
    else canonicalCartanReverse mu nu hmu hnu hinc

@[simp] theorem canonicalForward_self (mu : Fin d → ℕ) (hmu : Antitone mu)
    (hinc : Antitone (fun i => (mu i : ℝ) - (mu i : ℝ))) :
    canonicalForward mu mu hmu hmu hinc = TraceCloning.identityChannel := by
  simp [canonicalForward]

@[simp] theorem canonicalReverse_self (mu : Fin d → ℕ) (hmu : Antitone mu)
    (hinc : Antitone (fun i => (mu i : ℝ) - (mu i : ℝ))) :
    canonicalReverse mu mu hmu hmu hinc = TraceCloning.identityChannel := by
  simp [canonicalReverse]

/-- Actual finite CPTP maps with the quantitative bound, for every positive
spectral rank and including coincident rows. -/
theorem canonical_cloning_error_all_ranks
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
        Theorem2.cloningConstant d (cloningCountRank d r) s.qx * (D : ℝ) / (b + 1) ∧
    traceDistance ((canonicalReverse mu nu hmu hnu hinc).toFun
        ((canonicalWeightModel nu).relativeState (fun j => s.adjacentRatio j.val)))
      ((canonicalWeightModel mu).relativeState (fun j => s.adjacentRatio j.val)) ≤
        Theorem2.cloningConstant d (cloningCountRank d r) s.qx * (D : ℝ) / (b + 1) := by
  classical
  by_cases he : nu = mu
  · subst nu
    have hbnd : 0 ≤ Theorem2.cloningConstant d (cloningCountRank d r) s.qx * (D : ℝ) / (b + 1) :=
      div_nonneg (mul_nonneg (Theorem2.cloningConstant_nonneg _ _ _ s.qx_nonneg s.qx_lt_one)
        (Nat.cast_nonneg _)) (by linarith)
    simpa [canonicalForward, canonicalReverse, traceDistance, traceNorm, OrbitMemory.tr] using And.intro hbnd hbnd
  · have hD : 1 ≤ D := by
      have hnorm := differenceNorm_cast mu nu
      have hpos := differenceNorm_pos mu nu he
      have hle : differenceNorm mu nu ≤ D := by exact_mod_cast (hnorm ▸ hDnorm)
      omega
    simp only [canonicalForward, canonicalReverse, dif_neg he]
    by_cases hr1 : r = 1
    · have h := canonical_cloning_error_ambient_of_auxiliary s hd mu nu hmu hnu
        (canonicalAuxiliaryModel mu nu) (canonicalAuxiliaryModel_hrow mu nu hmu hnu hinc)
        hinc hzero D g b hD hb hbg hDnorm hgap
      simpa only [cloningCountRank, hr1, if_true, canonicalCartanForward, canonicalCartanReverse] using h
    · have hr : 2 ≤ r := by have hp := s.rank_pos; omega
      simpa only [cloningCountRank, hr1, if_false] using
        canonical_cloning_error s hr mu nu hmu hnu hinc hzero D g b hD hb hbg hDnorm hgap

/-- The complete diagonal-state Theorem 2 with the exact row L1 difference
and minimum adjacent gap computed from the actual highest rows. -/
theorem canonical_cloning_error_rows
    (s : FixedSpectrum d r) (hd : 2 ≤ d)
    (mu nu : Fin d → ℕ) (hmu : Antitone mu) (hnu : Antitone nu)
    (hinc : Antitone (fun i => (nu i : ℝ) - (mu i : ℝ)))
    (hzero : ∀ i : Fin d, r ≤ i.val → nu i = mu i) :
    traceDistance ((canonicalForward mu nu hmu hnu hinc).toFun
        ((canonicalWeightModel mu).relativeState (fun j => s.adjacentRatio j.val)))
      ((canonicalWeightModel nu).relativeState (fun j => s.adjacentRatio j.val)) ≤
        Theorem2.cloningConstant d (cloningCountRank d r) s.qx * (differenceNorm mu nu : ℝ) /
          ((minimumRowGap mu r hd s.rank_pos : ℝ) + 1) ∧
    traceDistance ((canonicalReverse mu nu hmu hnu hinc).toFun
        ((canonicalWeightModel nu).relativeState (fun j => s.adjacentRatio j.val)))
      ((canonicalWeightModel mu).relativeState (fun j => s.adjacentRatio j.val)) ≤
        Theorem2.cloningConstant d (cloningCountRank d r) s.qx * (differenceNorm mu nu : ℝ) /
          ((minimumRowGap mu r hd s.rank_pos : ℝ) + 1) := by
  exact canonical_cloning_error_all_ranks s hd mu nu hmu hnu hinc hzero
    (differenceNorm mu nu) (minimumRowGap mu r hd s.rank_pos) _ (Nat.cast_nonneg _) le_rfl
    (differenceNorm_cast mu nu).ge (minimumRowGap_cast_le mu hmu r hd s.rank_pos)

end FreeEntropy.ExteriorRepresentation
