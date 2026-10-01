/-
Copyright (c) 2026 Free Entropy formalization contributors.
See LICENSE and NOTICE in the repository root for license and attribution.
-/

import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Topology.Algebra.Star.Unitary
import Mathlib.MeasureTheory.Measure.Haar.Basic

/-!
# Probability Haar measure on the actual finite-dimensional unitary group

Compactness follows from closedness of the unitary equations and the bound
one on every matrix entry. Haar measure is normalized on the whole group.
-/

noncomputable section
open Set Matrix MeasureTheory TopologicalSpace

namespace FreeEntropy.UnitaryHaar

variable (n : Type*) [Fintype n] [DecidableEq n]

theorem isCompact_unitaryGroup :
    IsCompact (Matrix.unitaryGroup n ℂ : Set (Matrix n n ℂ)) := by
  apply (isCompact_closedBall (0 : ℂ) 1).matrix.of_isClosed_subset isClosed_unitary
  intro U hU
  change ∀ i j, U i j ∈ Metric.closedBall (0 : ℂ) 1
  intro i j
  simpa only [Metric.mem_closedBall, dist_zero_right] using entry_norm_bound_of_unitary hU i j

instance compactSpace : CompactSpace (Matrix.unitaryGroup n ℂ) :=
  isCompact_iff_compactSpace.mp (isCompact_unitaryGroup n)

example : IsTopologicalGroup (Matrix.unitaryGroup n ℂ) := inferInstance

instance measurableSpace : MeasurableSpace (Matrix.unitaryGroup n ℂ) := borel _
instance borelSpace : BorelSpace (Matrix.unitaryGroup n ℂ) := ⟨rfl⟩

/-- The entire compact unitary group as a positive compact set. -/
def wholeGroup : PositiveCompacts (Matrix.unitaryGroup n ℂ) :=
  ⟨⟨Set.univ, isCompact_univ⟩, by simp⟩

/-- Haar measure normalized to mass one on the actual unitary group. -/
def probabilityHaar : Measure (Matrix.unitaryGroup n ℂ) :=
  Measure.haarMeasure (wholeGroup n)

instance : IsProbabilityMeasure (probabilityHaar n) where
  measure_univ := Measure.haarMeasure_self

instance : (probabilityHaar n).IsMulLeftInvariant := by
  unfold probabilityHaar
  infer_instance

instance : (probabilityHaar n).IsHaarMeasure := by
  unfold probabilityHaar
  infer_instance

instance : (probabilityHaar n).Regular := by
  unfold probabilityHaar
  infer_instance

end FreeEntropy.UnitaryHaar
