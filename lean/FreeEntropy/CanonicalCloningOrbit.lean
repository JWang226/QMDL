/-
Copyright (c) 2026 Free Entropy formalization contributors.
See LICENSE and NOTICE in the repository root for license and attribution.
-/

import FreeEntropy.CanonicalFullCloning
import FreeEntropy.CanonicalCartanCovariance

/-! Actual covariance and exact orbit-error invariance of the constructed
canonical cloning channels, including the coincident-row identity branch. -/
noncomputable section
open Matrix
open scoped MatrixOrder ComplexOrder
namespace FreeEntropy.ExteriorRepresentation
open Channels TraceDistance
set_option backward.isDefEq.respectTransparency false
variable {d r : ℕ}

theorem canonicalForward_covariant (mu nu : Fin d → ℕ)
    (hmu : Antitone mu) (hnu : Antitone nu)
    (hinc : Antitone (fun i => (nu i : ℝ) - (mu i : ℝ))) (hd : 0 < d)
    (U : Matrix.unitaryGroup (Fin d) ℂ) (X : Matrix (IrrepIndex mu) (IrrepIndex mu) ℂ) :
    (canonicalForward mu nu hmu hnu hinc).toFun
      (canonicalWeightRepresentation mu U * X * (canonicalWeightRepresentation mu U)ᴴ) =
    canonicalWeightRepresentation nu U * (canonicalForward mu nu hmu hnu hinc).toFun X *
      (canonicalWeightRepresentation nu U)ᴴ := by
  classical
  by_cases h : nu = mu
  · subst nu
    simp only [canonicalForward_self]
    simp only [TraceCloning.identityChannel_apply]
  · simpa only [canonicalForward, dif_neg h] using
      canonicalCartanForward_covariant mu nu hmu hnu hinc hd U X

theorem canonicalReverse_covariant (mu nu : Fin d → ℕ)
    (hmu : Antitone mu) (hnu : Antitone nu)
    (hinc : Antitone (fun i => (nu i : ℝ) - (mu i : ℝ))) (hd : 0 < d)
    (U : Matrix.unitaryGroup (Fin d) ℂ) (X : Matrix (IrrepIndex nu) (IrrepIndex nu) ℂ) :
    (canonicalReverse mu nu hmu hnu hinc).toFun
      (canonicalWeightRepresentation nu U * X * (canonicalWeightRepresentation nu U)ᴴ) =
    canonicalWeightRepresentation mu U * (canonicalReverse mu nu hmu hnu hinc).toFun X *
      (canonicalWeightRepresentation mu U)ᴴ := by
  classical
  by_cases h : nu = mu
  · subst nu
    simp only [canonicalReverse_self]
    simp only [TraceCloning.identityChannel_apply]
  · simpa only [canonicalReverse, dif_neg h] using
      canonicalCartanReverse_covariant mu nu hmu hnu hinc hd U X

/-- The forward cloning error is constant on the full physical unitary orbit. -/
theorem canonicalForward_orbit_error_eq (s : FixedSpectrum d r) (hd : 2 ≤ d)
    (mu nu : Fin d → ℕ) (hmu : Antitone mu) (hnu : Antitone nu)
    (hinc : Antitone (fun i => (nu i : ℝ) - (mu i : ℝ)))
    (U : Matrix.unitaryGroup (Fin d) ℂ) :
    traceDistance ((canonicalForward mu nu hmu hnu hinc).toFun (canonicalOrbitState s mu U))
      (canonicalOrbitState s nu U) =
    traceDistance ((canonicalForward mu nu hmu hnu hinc).toFun
        ((canonicalWeightModel mu).relativeState (fun j => s.adjacentRatio j.val)))
      ((canonicalWeightModel nu).relativeState (fun j => s.adjacentRatio j.val)) := by
  rw [canonicalOrbitState, canonicalForward_covariant mu nu hmu hnu hinc (by omega)]
  exact traceDistance_isometry _ (canonicalWeightRepresentation_unitary nu U)
    ((canonicalForward mu nu hmu hnu hinc).positive _ (canonicalRelativeState_positive s mu hd))
    (canonicalRelativeState_positive s nu hd)

/-- The reverse cloning error is constant on the full physical unitary orbit. -/
theorem canonicalReverse_orbit_error_eq (s : FixedSpectrum d r) (hd : 2 ≤ d)
    (mu nu : Fin d → ℕ) (hmu : Antitone mu) (hnu : Antitone nu)
    (hinc : Antitone (fun i => (nu i : ℝ) - (mu i : ℝ)))
    (U : Matrix.unitaryGroup (Fin d) ℂ) :
    traceDistance ((canonicalReverse mu nu hmu hnu hinc).toFun (canonicalOrbitState s nu U))
      (canonicalOrbitState s mu U) =
    traceDistance ((canonicalReverse mu nu hmu hnu hinc).toFun
        ((canonicalWeightModel nu).relativeState (fun j => s.adjacentRatio j.val)))
      ((canonicalWeightModel mu).relativeState (fun j => s.adjacentRatio j.val)) := by
  rw [canonicalOrbitState, canonicalReverse_covariant mu nu hmu hnu hinc (by omega)]
  exact traceDistance_isometry _ (canonicalWeightRepresentation_unitary mu U)
    ((canonicalReverse mu nu hmu hnu hinc).positive _ (canonicalRelativeState_positive s nu hd))
    (canonicalRelativeState_positive s mu hd)

end FreeEntropy.ExteriorRepresentation
