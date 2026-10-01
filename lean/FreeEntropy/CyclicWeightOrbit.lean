/-
Copyright (c) 2026 Free Entropy formalization contributors.
See LICENSE and NOTICE in the repository root for license and attribution.
-/

import FreeEntropy.CyclicWeightStates
import FreeEntropy.GeometricOrbit
import FreeEntropy.GTOrbit

/-! The converse spectral data for an actual cyclic representation. Every
count and eigenvalue estimate is derived from its Lie action. -/
noncomputable section
open scoped BigOperators Matrix.Norms.Elementwise Topology
open Matrix MeasureTheory MeasureTheory.Measure
namespace FreeEntropy.CartanLieCloning
set_option backward.isDefEq.respectTransparency false
variable {d r : ℕ} {A B : Type*} [Fintype A] [DecidableEq A] [Nonempty A]
  [Fintype B] [DecidableEq B]

def CyclicWeightModel.orbitWeights (M : CyclicWeightModel d A) (hd : 2 ≤ d)
    (ratio : Fin (d - 1) → ℝ) (q : ℝ)
    (hratio : ∀ j, 0 ≤ ratio j) (hbound : ∀ j, ratio j ≤ q) :
    GeometricOrbit.WeightData A (d.choose 2) q where
  weight := M.relativeWeight ratio
  depth := M.basisDepth
  highest := M.highestBasis
  nonneg := M.relativeWeight_nonneg ratio hratio
  highest_weight := M.relativeWeight_highest ratio
  other_depth a ha := Nat.one_le_iff_ne_zero.mpr (fun h => ha ((M.basisDepth_eq_zero_iff a).mp h))
  envelope := M.relativeWeight_envelope ratio q hratio hbound
  count t := by simpa only [Finset.sum_const, smul_eq_mul, mul_one, Fintype.card_subtype]
    using M.depthMultiplicity_le hd t

@[simp] theorem CyclicWeightModel.orbitWeights_normalizer (M : CyclicWeightModel d A)
    (hd : 2 ≤ d) (ratio : Fin (d - 1) → ℝ) (q : ℝ)
    (hratio : ∀ j, 0 ≤ ratio j) (hbound : ∀ j, ratio j ≤ q) :
    (M.orbitWeights hd ratio q hratio hbound).normalizer = M.relativeNormalizer ratio := by
  simp [GeometricOrbit.WeightData.normalizer, WeightNormalization.partitionFunction,
    orbitWeights, relativeNormalizer]

@[simp] theorem CyclicWeightModel.orbitWeights_state (M : CyclicWeightModel d A)
    (hd : 2 ≤ d) (ratio : Fin (d - 1) → ℝ) (q : ℝ)
    (hratio : ∀ j, 0 ≤ ratio j) (hbound : ∀ j, ratio j ≤ q) :
    (M.orbitWeights hd ratio q hratio hbound).state = M.relativeState ratio := by
  simp only [GeometricOrbit.WeightData.state, M.orbitWeights_normalizer]
  rfl

def CyclicWeightModel.spectrumWeights (M : CyclicWeightModel d A)
    (s : FixedSpectrum d r) (hd : 2 ≤ d) : GeometricOrbit.WeightData A (d.choose 2) s.qx :=
  M.orbitWeights hd (fun j => s.adjacentRatio j.val) s.qx
    (fun j => s.adjacentRatio_nonneg j.val) (fun j => GTOrbit.adjacentRatio_le_qx s j.val)

theorem CyclicWeightModel.actual_uniform_gap (M : CyclicWeightModel d A)
    (s : FixedSpectrum d r) (hd : 2 ≤ d) :
    0 < (1 - s.qx) ^ (d.choose 2 + 1) ∧
      (1 - s.qx) ^ (d.choose 2 + 1) ≤
        1 / M.relativeNormalizer (fun j => s.adjacentRatio j.val) -
          s.qx * (1 / M.relativeNormalizer (fun j => s.adjacentRatio j.val)) := by
  simpa only [spectrumWeights, M.orbitWeights_normalizer] using
    (M.spectrumWeights s hd).gap_lower (Nat.choose_pos hd) s.qx_nonneg s.qx_lt_one

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [MeasurableSpace G] [BorelSpace G]

/-- The finite memory converse for the literal normalized weight state.
There is no weight-count, normalization, or spectral-gap hypothesis. -/
theorem CyclicWeightModel.actual_orbit_memory_bound (M : CyclicWeightModel d A)
    (s : FixedSpectrum d r) (hd : 2 ≤ d)
    (haar : Measure G) [IsMulLeftInvariant haar] [IsProbabilityMeasure haar]
    (U : G →* Matrix A A ℂ) (hU : Continuous U)
    (hunitary : ∀ g, (U g)ᴴ * U g = 1)
    [Representation.IsIrreducible (Twirling.matrixRepresentation U)]
    (E : Channels.MatrixChannel A B) (D : Channels.MatrixChannel B A) :
    (Fintype.card A : ℝ) * (1 -
      (∫ g, TraceDistance.traceDistance
        (D.toFun (E.toFun (U g * M.relativeState (fun j => s.adjacentRatio j.val) * (U g)ᴴ)))
        (U g * M.relativeState (fun j => s.adjacentRatio j.val) * (U g)ᴴ) ∂haar) /
          (1 - s.qx) ^ (d.choose 2 + 1)) ≤ (Fintype.card B : ℝ) := by
  simpa only [spectrumWeights, M.orbitWeights_state] using
    GeometricOrbit.memory_bound haar (M.spectrumWeights s hd) (Nat.choose_pos hd)
      s.qx_nonneg s.qx_lt_one U hU hunitary E D

end FreeEntropy.CartanLieCloning
