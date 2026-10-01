/-
Copyright (c) 2026 Free Entropy formalization contributors.
See LICENSE and NOTICE in the repository root for license and attribution.
-/
import FreeEntropy.CanonicalChoi
import FreeEntropy.CanonicalReverseChoi
import FreeEntropy.CanonicalCloningBounds
import FreeEntropy.ChoiContraction

/-!
Independent expected Theorem 2 statement with the literal Choi-contraction maps
redeclared below. The constructed representation, normalized orbit state, and
PRV projector definitions form an explicit trusted-definition boundary; see
trusted-boundary.json. Neither final Theorem2Canonical nor Theorem2Choi is imported.
The sole `sorry` is an intentional Comparator challenge hole.
-/
noncomputable section
open Matrix
open scoped Kronecker
namespace FreeEntropy.ExteriorRepresentation
open CartanChoi TraceDistance
set_option backward.isDefEq.respectTransparency false
variable {d r : ℕ}

def prvForward (mu nu : Fin d → ℕ) (hmu : Antitone mu) (hnu : Antitone nu)
    (hinc : Antitone (fun i => (nu i : ℝ) - (mu i : ℝ)))
    (X : Matrix (IrrepIndex mu) (IrrepIndex mu) ℂ) :
    Matrix (IrrepIndex nu) (IrrepIndex nu) ℂ :=
  partialTraceInput
    ((((Fintype.card (IrrepIndex mu) : ℝ) /
      Fintype.card (IrrepIndex (auxiliaryRow mu nu))) •
      canonicalChoiProjector mu nu hmu hnu hinc) * (X.transpose ⊗ₖ 1))

def prvReverse (mu nu : Fin d → ℕ) (hmu : Antitone mu) (hnu : Antitone nu)
    (hinc : Antitone (fun i => (nu i : ℝ) - (mu i : ℝ)))
    (Y : Matrix (IrrepIndex nu) (IrrepIndex nu) ℂ) :
    Matrix (IrrepIndex mu) (IrrepIndex mu) ℂ :=
  partialTraceInput
    ((((Fintype.card (IrrepIndex nu) : ℝ) /
      Fintype.card (IrrepIndex (auxiliaryRow mu nu))) •
      canonicalReverseChoiProjector mu nu hmu hnu hinc) * (Y.transpose ⊗ₖ 1))

theorem theorem2_cloning_accuracy_choi
    (s : FixedSpectrum d r) (hd : 2 ≤ d)
    (mu nu : Fin d → ℕ) (hmu : Antitone mu) (hnu : Antitone nu)
    (hmu_support : ∀ i : Fin d, r ≤ i.val → mu i = 0)
    (hnu_support : ∀ i : Fin d, r ≤ i.val → nu i = 0)
    (hinc : Antitone (fun i => (nu i : ℝ) - (mu i : ℝ)))
    (U : Matrix.unitaryGroup (Fin d) ℂ) :
    traceDistance (prvForward mu nu hmu hnu hinc (canonicalOrbitState s mu U))
      (canonicalOrbitState s nu U) ≤
        Theorem2.cloningConstant d r s.qx * (differenceNorm mu nu : ℝ) /
          ((minimumRowGap mu r hd s.rank_pos : ℝ) + 1) ∧
    traceDistance (prvReverse mu nu hmu hnu hinc (canonicalOrbitState s nu U))
      (canonicalOrbitState s mu U) ≤
        Theorem2.cloningConstant d r s.qx * (differenceNorm mu nu : ℝ) /
          ((minimumRowGap mu r hd s.rank_pos : ℝ) + 1) := by
  sorry

end FreeEntropy.ExteriorRepresentation
