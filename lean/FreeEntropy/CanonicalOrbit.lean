/-
Copyright (c) 2026 Free Entropy formalization contributors.
See LICENSE and NOTICE in the repository root for license and attribution.
-/

import FreeEntropy.CyclicWeightOrbit
import FreeEntropy.ExteriorWeightCoordinates
import FreeEntropy.UnitaryCoordinates

/-! The literal canonical unitary orbit, in its actual weight coordinates.
The spectral gap, positivity, normalization and irreducibility are proved
from the constructed representation, without representation model inputs. -/
noncomputable section
open Matrix MeasureTheory MeasureTheory.Measure
open scoped Matrix.Norms.Elementwise Topology ComplexOrder MatrixOrder
namespace FreeEntropy.ExteriorRepresentation
open CartanLieCloning
set_option backward.isDefEq.respectTransparency false
variable {d r : ℕ}
local instance orbitIndex_nonempty (mu : Fin d → ℕ) : Nonempty (IrrepIndex mu) :=
  Fin.pos_iff_nonempty.mp (irrep_dimension_pos mu)

def canonicalWeightRepresentation (mu : Fin d → ℕ) :
    Matrix.unitaryGroup (Fin d) ℂ →* Matrix (IrrepIndex mu) (IrrepIndex mu) ℂ :=
  UnitaryCoordinates.representation (irrepMatrix mu)
    (canonicalWeightCoordinates mu).unitary (canonicalWeightCoordinates mu).isometry

theorem canonicalWeightRepresentation_unitary (mu : Fin d → ℕ)
    (U : Matrix.unitaryGroup (Fin d) ℂ) :
    (canonicalWeightRepresentation mu U)ᴴ * canonicalWeightRepresentation mu U = 1 :=
  UnitaryCoordinates.unitary _ _ _ (irrepMatrix_unitary mu) U

theorem canonicalWeightRepresentation_continuous (mu : Fin d → ℕ) :
    Continuous (canonicalWeightRepresentation mu) :=
  UnitaryCoordinates.continuous _ _ _ (irrepMatrix_continuous mu)

theorem canonicalWeightRepresentation_irreducible (mu : Fin d → ℕ) :
    Representation.IsIrreducible (Twirling.matrixRepresentation (canonicalWeightRepresentation mu)) :=
  UnitaryCoordinates.irreducible _ _ _ (irrepMatrix_irreducible mu)

def canonicalOrbitState (s : FixedSpectrum d r) (mu : Fin d → ℕ)
    (U : Matrix.unitaryGroup (Fin d) ℂ) : Matrix (IrrepIndex mu) (IrrepIndex mu) ℂ :=
  canonicalWeightRepresentation mu U *
    (canonicalWeightModel mu).relativeState (fun j => s.adjacentRatio j.val) *
    (canonicalWeightRepresentation mu U)ᴴ

theorem canonicalRelativeState_positive (s : FixedSpectrum d r) (mu : Fin d → ℕ) (hd : 2 ≤ d) :
    ((canonicalWeightModel mu).relativeState (fun j => s.adjacentRatio j.val)).PosSemidef := by
  have h := ((canonicalWeightModel mu).spectrumWeights s hd).state_positive
  simpa only [CyclicWeightModel.spectrumWeights, CyclicWeightModel.orbitWeights_state] using h

theorem canonicalRelativeState_trace (s : FixedSpectrum d r) (mu : Fin d → ℕ) (hd : 2 ≤ d) :
    ((canonicalWeightModel mu).relativeState (fun j => s.adjacentRatio j.val)).trace = 1 := by
  have h := ((canonicalWeightModel mu).spectrumWeights s hd).state_trace
  simpa only [CyclicWeightModel.spectrumWeights, CyclicWeightModel.orbitWeights_state] using h

theorem canonicalOrbitState_positive (s : FixedSpectrum d r) (mu : Fin d → ℕ) (hd : 2 ≤ d)
    (U : Matrix.unitaryGroup (Fin d) ℂ) : (canonicalOrbitState s mu U).PosSemidef :=
  (canonicalRelativeState_positive s mu hd).mul_mul_conjTranspose_same _

theorem canonicalOrbitState_trace (s : FixedSpectrum d r) (mu : Fin d → ℕ) (hd : 2 ≤ d)
    (U : Matrix.unitaryGroup (Fin d) ℂ) : (canonicalOrbitState s mu U).trace = 1 := by
  rw [canonicalOrbitState, Matrix.trace_mul_cycle, canonicalWeightRepresentation_unitary,
    Matrix.one_mul, canonicalRelativeState_trace s mu hd]

theorem canonicalOrbitState_continuous (s : FixedSpectrum d r) (mu : Fin d → ℕ) :
    Continuous (canonicalOrbitState s mu) :=
  ((canonicalWeightRepresentation_continuous mu).matrix_mul continuous_const).matrix_mul
    (canonicalWeightRepresentation_continuous mu).matrix_conjTranspose

/-- Actual canonical-orbit converse: every finite quantum code obeys the
bound. The only measure input is normalized Haar measure on U(d). -/
theorem canonical_orbit_memory_bound (s : FixedSpectrum d r) (mu : Fin d → ℕ) (hd : 2 ≤ d)
    {B : Type*} [Fintype B] [DecidableEq B]
    (haar : Measure (Matrix.unitaryGroup (Fin d) ℂ))
    [IsMulLeftInvariant haar] [IsProbabilityMeasure haar]
    (E : Channels.MatrixChannel (IrrepIndex mu) B)
    (D : Channels.MatrixChannel B (IrrepIndex mu)) :
    (Module.finrank ℂ (highestSubspace mu) : ℝ) * (1 -
      (∫ U, TraceDistance.traceDistance
        (D.toFun (E.toFun (canonicalOrbitState s mu U))) (canonicalOrbitState s mu U) ∂haar) /
          (1 - s.qx) ^ (d.choose 2 + 1)) ≤ (Fintype.card B : ℝ) := by
  letI := canonicalWeightRepresentation_irreducible mu
  simpa only [Fintype.card_fin, canonicalOrbitState] using
    (canonicalWeightModel mu).actual_orbit_memory_bound s hd haar
      (canonicalWeightRepresentation mu) (canonicalWeightRepresentation_continuous mu)
      (canonicalWeightRepresentation_unitary mu) E D

end FreeEntropy.ExteriorRepresentation
