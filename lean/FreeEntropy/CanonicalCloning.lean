/-
Copyright (c) 2026 Free Entropy formalization contributors.
See LICENSE and NOTICE in the repository root for license and attribution.
-/

import FreeEntropy.CanonicalCloningCore
import FreeEntropy.SignedAuxiliaryModel
import FreeEntropy.CanonicalRowBounds

/-! Actual canonical cloning channels and their finite Theorem 2 bound.
The auxiliary representation for an arbitrary dominant signed difference
is constructed by a determinant shift of an exterior-power model. -/
noncomputable section
open Matrix
open scoped BigOperators
namespace FreeEntropy.ExteriorRepresentation
open CartanLieCloning CasimirWeights TraceDistance
set_option backward.isDefEq.respectTransparency false
variable {d r : ℕ}
local instance (mu : Fin d → ℕ) : Nonempty (IrrepIndex mu) :=
  Fin.pos_iff_nonempty.mp (irrep_dimension_pos mu)

def canonicalCartanForward (mu nu : Fin d → ℕ) (hmu : Antitone mu) (hnu : Antitone nu)
    (hinc : Antitone (fun i => (nu i : ℝ) - (mu i : ℝ))) :
    Channels.MatrixChannel (IrrepIndex mu) (IrrepIndex nu) :=
  specifiedForward (canonicalWeightModel mu) (canonicalAuxiliaryModel mu nu) (canonicalWeightModel nu)
    (canonicalAuxiliaryModel_hrow mu nu hmu hnu hinc)

def canonicalCartanReverse (mu nu : Fin d → ℕ) (hmu : Antitone mu) (hnu : Antitone nu)
    (hinc : Antitone (fun i => (nu i : ℝ) - (mu i : ℝ))) :
    Channels.MatrixChannel (IrrepIndex nu) (IrrepIndex mu) :=
  specifiedReverse (canonicalWeightModel mu) (canonicalAuxiliaryModel mu nu) (canonicalWeightModel nu)
    (canonicalAuxiliaryModel_hrow mu nu hmu hnu hinc)

/-- Fully constructed canonical Theorem 2, for positive row difference.
Only the manuscript's scalar row/rank/gap conditions are hypotheses. -/
theorem canonical_cloning_error
    (s : FixedSpectrum d r) (hr : 2 ≤ r)
    (mu nu : Fin d → ℕ) (hmu : Antitone mu) (hnu : Antitone nu)
    (hinc : Antitone (fun i => (nu i : ℝ) - (mu i : ℝ)))
    (hzero : ∀ i : Fin d, r ≤ i.val → nu i = mu i)
    (D g : ℕ) (b : ℝ) (hD : 1 ≤ D) (hb : 0 ≤ b) (hbg : b ≤ (g : ℝ))
    (hDnorm : l1 (fun i => (nu i : ℝ) - (mu i : ℝ)) ≤ (D : ℝ))
    (hgap : ∀ j : Fin (d - 1), j.val < r →
      (g : ℝ) ≤ (mu (left j) : ℝ) - (mu (right j) : ℝ)) :
    traceDistance ((canonicalCartanForward mu nu hmu hnu hinc).toFun
        ((canonicalWeightModel mu).relativeState (fun j => s.adjacentRatio j.val)))
      ((canonicalWeightModel nu).relativeState (fun j => s.adjacentRatio j.val)) ≤
        Theorem2.cloningConstant d r s.qx * (D : ℝ) / (b + 1) ∧
    traceDistance ((canonicalCartanReverse mu nu hmu hnu hinc).toFun
        ((canonicalWeightModel nu).relativeState (fun j => s.adjacentRatio j.val)))
      ((canonicalWeightModel mu).relativeState (fun j => s.adjacentRatio j.val)) ≤
        Theorem2.cloningConstant d r s.qx * (D : ℝ) / (b + 1) :=
  canonical_cloning_error_of_auxiliary s hr mu nu hmu hnu (canonicalAuxiliaryModel mu nu)
    (canonicalAuxiliaryModel_hrow mu nu hmu hnu hinc) hinc hzero D g b hD hb hbg hDnorm hgap

end FreeEntropy.ExteriorRepresentation
