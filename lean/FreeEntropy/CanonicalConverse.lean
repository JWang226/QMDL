/-
Copyright (c) 2026 Free Entropy formalization contributors.
See LICENSE and NOTICE in the repository root for license and attribution.
-/

import FreeEntropy.CanonicalOrbit
import FreeEntropy.CanonicalDimension
import FreeEntropy.UnitaryHaar

/-! The exact asymptotic converse for the actual canonical memory orbit.
Both its dimension and its positive spectral gap are derived. -/
noncomputable section
open Matrix MeasureTheory MeasureTheory.Measure Filter
open scoped Topology Matrix.Norms.Elementwise
namespace FreeEntropy.ExteriorRepresentation
set_option backward.isDefEq.respectTransparency false
variable {d r : ℕ}

abbrev targetCanonicalRow (s : FixedSpectrum d r) (n : ℕ) : Fin d → ℕ :=
  fun i => targetNaturalRow s n i.val

def canonicalAverageError (s : FixedSpectrum d r) (mu : Fin d → ℕ)
    {B : Type*} [Fintype B] [DecidableEq B]
    (E : Channels.MatrixChannel (IrrepIndex mu) B)
    (D : Channels.MatrixChannel B (IrrepIndex mu)) : ℝ :=
  ∫ U, TraceDistance.traceDistance (D.toFun (E.toFun (canonicalOrbitState s mu U)))
    (canonicalOrbitState s mu U) ∂UnitaryHaar.probabilityHaar (Fin d)

/-- Any code for the actual padded canonical orbit with vanishing average
error has the precise qmdl lower bound. No dimension, gap, character,
twirling, or scalar-memory-bound premise remains. -/
theorem theorem1_canonical_orbit_converse (s : FixedSpectrum d r) (hd : 2 ≤ d)
    (memory : ℕ → ℕ)
    (E : ∀ n, Channels.MatrixChannel (IrrepIndex (targetCanonicalRow s n)) (Fin (memory n)))
    (D : ∀ n, Channels.MatrixChannel (Fin (memory n)) (IrrepIndex (targetCanonicalRow s n)))
    (herror : Tendsto (fun n => canonicalAverageError s (targetCanonicalRow s n) (E n) (D n))
      atTop (𝓝 0)) :
    (0 : EReal) ≤ liminf
      (fun n => ((Real.logb 2 (memory n) - Weyl.qmdl d r s.eigenvalue n : ℝ) : EReal)) atTop := by
  apply theorem1_converse_of_quantum_estimates s memory (targetCanonicalDimension s)
    (fun n => canonicalAverageError s (targetCanonicalRow s n) (E n) (D n))
    (fun _ => 0) ((1 - s.qx) ^ (d.choose 2 + 1))
    (Eventually.of_forall (targetCanonicalDimension_weyl s)) (targetCanonicalDimension_pos s)
    (pow_pos (sub_pos.mpr s.qx_lt_one) _) herror (Asymptotics.isBigO_zero _ _) ?_
  exact Eventually.of_forall (fun n => by
    simpa only [add_zero, canonicalAverageError, targetCanonicalDimension, Fintype.card_fin] using
      canonical_orbit_memory_bound s (targetCanonicalRow s n) hd
        (UnitaryHaar.probabilityHaar (Fin d)) (E n) (D n))

end FreeEntropy.ExteriorRepresentation
