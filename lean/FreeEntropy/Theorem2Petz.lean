/-
Copyright (c) 2026 Free Entropy formalization contributors.
See LICENSE and NOTICE in the repository root for license and attribution.
-/

import FreeEntropy.Theorem2Canonical
import FreeEntropy.CanonicalPetz

/-! Theorem 2 with the reverse channel written as the literal Petz recovery
expression for the actual forward cloner and its maximally mixed input. -/
noncomputable section
open Matrix
namespace FreeEntropy.ExteriorRepresentation
open TraceDistance MultiplicityChannels
set_option backward.isDefEq.respectTransparency false
variable {d r : ℕ}

/-- Both manuscript cloning bounds, with the reverse map expressed using
its actual Hilbert--Schmidt adjoint, matrix square roots and inverses.
The adjoint and Petz identities are proved, not premises. -/
theorem theorem2_cloning_accuracy_petz
    (s : FixedSpectrum d r) (hd : 2 ≤ d)
    (mu nu : Fin d → ℕ) (hmu : Antitone mu) (hnu : Antitone nu)
    (hmu_support : ∀ i : Fin d, r ≤ i.val → mu i = 0)
    (hnu_support : ∀ i : Fin d, r ≤ i.val → nu i = 0)
    (hinc : Antitone (fun i => (nu i : ℝ) - (mu i : ℝ)))
    (U : Matrix.unitaryGroup (Fin d) ℂ) :
    traceDistance ((canonicalForward mu nu hmu hnu hinc).toFun (canonicalOrbitState s mu U))
      (canonicalOrbitState s nu U) ≤
        Theorem2.cloningConstant d r s.qx * (differenceNorm mu nu : ℝ) /
          ((minimumRowGap mu r hd s.rank_pos : ℝ) + 1) ∧
    traceDistance
      (Petz.recovery (canonicalForward mu nu hmu hnu hinc) (canonicalAdjoint mu nu hmu hnu hinc)
        (maximallyMixed (IrrepIndex mu)) (canonicalOrbitState s nu U))
      (canonicalOrbitState s mu U) ≤
        Theorem2.cloningConstant d r s.qx * (differenceNorm mu nu : ℝ) /
          ((minimumRowGap mu r hd s.rank_pos : ℝ) + 1) := by
  rw [canonicalPetz_eq_reverse mu nu hmu hnu hinc (by omega)]
  exact theorem2_cloning_accuracy s hd mu nu hmu hnu hmu_support hnu_support hinc U

end FreeEntropy.ExteriorRepresentation
