/-
Copyright (c) 2026 Free Entropy formalization contributors.
See LICENSE and NOTICE in the repository root for license and attribution.
-/

import FreeEntropy.CanonicalCloningBounds
import FreeEntropy.CanonicalCloningOrbit
import FreeEntropy.CanonicalCloningSelf

/-! Theorem 2 for the literal canonical unitary orbits. The highest-weight
representations, CPTP cloning maps, Weyl dimensions, weight multiplicities,
normalization, covariance, and all trace-distance estimates are constructed
and proved. Only the hypotheses on the spectrum and the two highest rows
from the manuscript remain. -/
noncomputable section
open Matrix
namespace FreeEntropy.ExteriorRepresentation
open CartanLieCloning CasimirWeights TraceDistance
set_option backward.isDefEq.respectTransparency false
variable {d r : ℕ}

/-- A numerical-bound form of the actual covariant cloning theorem, useful
for uniform estimates over a family of typical source rows. -/
theorem canonical_cloning_accuracy_orbit_bounds
    (s : FixedSpectrum d r) (hd : 2 ≤ d)
    (mu nu : Fin d → ℕ) (hmu : Antitone mu) (hnu : Antitone nu)
    (hinc : Antitone (fun i => (nu i : ℝ) - (mu i : ℝ)))
    (hzero : ∀ i : Fin d, r ≤ i.val → nu i = mu i)
    (D g : ℕ) (b : ℝ) (hb : 0 ≤ b) (hbg : b ≤ (g : ℝ))
    (hDnorm : l1 (fun i => (nu i : ℝ) - (mu i : ℝ)) ≤ (D : ℝ))
    (hgap : ∀ j : Fin (d - 1), j.val < r →
      (g : ℝ) ≤ (mu (left j) : ℝ) - (mu (right j) : ℝ))
    (U : Matrix.unitaryGroup (Fin d) ℂ) :
    traceDistance ((canonicalForward mu nu hmu hnu hinc).toFun (canonicalOrbitState s mu U))
      (canonicalOrbitState s nu U) ≤ Theorem2.cloningConstant d r s.qx * (D : ℝ) / (b + 1) ∧
    traceDistance ((canonicalReverse mu nu hmu hnu hinc).toFun (canonicalOrbitState s nu U))
      (canonicalOrbitState s mu U) ≤ Theorem2.cloningConstant d r s.qx * (D : ℝ) / (b + 1) := by
  rw [canonicalForward_orbit_error_eq s hd mu nu hmu hnu hinc U,
    canonicalReverse_orbit_error_eq s hd mu nu hmu hnu hinc U]
  exact canonical_cloning_accuracy_bounds s hd mu nu hmu hnu hinc hzero D g b hb hbg hDnorm hgap

/-- **Theorem 2 (Cloning accuracy).** For every unitary eigenbasis, the two
actual CPTP channels have error at most `C(d,x) D / (bμ+1)`. The source and
target are the constructed normalized representation states. `D` is the
exact row L1 difference and `bμ` the exact minimum row gap. This includes
rank one, determinant-shifted signed differences, and `D=0`.

There are no representation-existence, dimension, weight-counting,
Casimir, covariance, state-normalization, or channel hypotheses. -/
theorem theorem2_cloning_accuracy
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
    traceDistance ((canonicalReverse mu nu hmu hnu hinc).toFun (canonicalOrbitState s nu U))
      (canonicalOrbitState s mu U) ≤
        Theorem2.cloningConstant d r s.qx * (differenceNorm mu nu : ℝ) /
          ((minimumRowGap mu r hd s.rank_pos : ℝ) + 1) := by
  rw [canonicalForward_orbit_error_eq s hd mu nu hmu hnu hinc U,
    canonicalReverse_orbit_error_eq s hd mu nu hmu hnu hinc U]
  exact canonical_cloning_accuracy_rows s hd mu nu hmu hnu hinc
    (fun i hi => (hnu_support i hi).trans (hmu_support i hi).symm)

/-- The same bound for the literal Cartan formulas, including coincident
rows: the formulas themselves become identity channels at zero difference. -/
theorem theorem2_cartan_cloning_accuracy
    (s : FixedSpectrum d r) (hd : 2 ≤ d)
    (mu nu : Fin d → ℕ) (hmu : Antitone mu) (hnu : Antitone nu)
    (hmu_support : ∀ i : Fin d, r ≤ i.val → mu i = 0)
    (hnu_support : ∀ i : Fin d, r ≤ i.val → nu i = 0)
    (hinc : Antitone (fun i => (nu i : ℝ) - (mu i : ℝ)))
    (U : Matrix.unitaryGroup (Fin d) ℂ) :
    traceDistance ((canonicalCartanForward mu nu hmu hnu hinc).toFun
      (canonicalOrbitState s mu U)) (canonicalOrbitState s nu U) ≤
        Theorem2.cloningConstant d r s.qx * (differenceNorm mu nu : ℝ) /
          ((minimumRowGap mu r hd s.rank_pos : ℝ) + 1) ∧
    traceDistance ((canonicalCartanReverse mu nu hmu hnu hinc).toFun
      (canonicalOrbitState s nu U)) (canonicalOrbitState s mu U) ≤
        Theorem2.cloningConstant d r s.qx * (differenceNorm mu nu : ℝ) /
          ((minimumRowGap mu r hd s.rank_pos : ℝ) + 1) := by
  have h := theorem2_cloning_accuracy s hd mu nu hmu hnu hmu_support hnu_support hinc U
  have hd0 : 0 < d := by omega
  rw [canonicalForward_eq_cartan_apply mu nu hmu hnu hinc hd0,
    canonicalReverse_eq_cartan_apply mu nu hmu hnu hinc hd0] at h
  exact h

end FreeEntropy.ExteriorRepresentation
