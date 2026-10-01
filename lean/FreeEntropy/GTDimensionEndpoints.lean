/-
Copyright (c) 2026 Free Entropy formalization contributors.
See LICENSE and NOTICE in the repository root for license and attribution.
-/

import FreeEntropy.GTDimensionFormula
import FreeEntropy.GTOrbit
import FreeEntropy.SchurAchievability

/-!
# Dimension-free hypotheses for the concrete GT endpoints

The memory register is the actual finite GT basis of the padded target.
Its dimension identity is a theorem, so the code and orbit results below
have no independent representation-dimension assumption.
-/

noncomputable section
open Filter MeasureTheory Matrix
open scoped BigOperators Topology Matrix.Norms.Elementwise
open FreeEntropy.TraceDistance FreeEntropy.Twirling

namespace FreeEntropy.SchurAchievability

/-- The actual Schur encoder/decoder with the padded GT memory. Local sector
cloning and diagram probability estimates imply the claimed asymptotics;
the memory dimension is computed from the actual finite basis. -/
theorem theorem1_schur_achievability_gt {d r : ℕ}
    (s : FixedSpectrum d r) (hd : 2 ≤ d)
    (code : ∀ n, Code (GTDimension.targetDimension s n)) (K : ℝ) (hK : 0 ≤ K)
    (hdiagrams : ∀ᶠ n in atTop, (code n).DiagramEstimate s n)
    (hf : ∀ᶠ n in atTop, ∀ i ∈ (code n).typical,
      traceDistance (((code n).forward i).toFun ((code n).state i)) (code n).target ≤
        cloningEnvelope s hd K n ((code n).row i))
    (hr : ∀ᶠ n in atTop, ∀ i ∈ (code n).typical,
      traceDistance (((code n).reverse i).toFun (code n).target) ((code n).state i) ≤
        cloningEnvelope s hd K n ((code n).row i)) :
    Tendsto (fun n => Real.logb 2 (GTDimension.targetDimension s n) -
      Weyl.qmdl d r s.eigenvalue n) atTop (𝓝 0) ∧
      Asymptotics.IsBigO atTop (fun n => (code n).error) Weyl.errorScale ∧
      Tendsto (fun n => (code n).error) atTop (𝓝 0) :=
  theorem1_schur_achievability_of_pointwise s hd (GTDimension.targetDimension s)
    code K hK (Eventually.of_forall (GTDimension.targetDimension_weyl s)) hdiagrams hf hr

end FreeEntropy.SchurAchievability

namespace FreeEntropy.GTOrbit
open GelfandTsetlin GTDimension

/-- The actual padded GT basis, in full ambient dimension even at deficient rank. -/
abbrev PaddedBasis {d r : ℕ} (s : FixedSpectrum d r) (n : ℕ) :=
  Pattern (fun i : Fin d => targetIntegerRow s n i.val)

local instance {d r : ℕ} {s : FixedSpectrum d r} {n : ℕ} :
    DecidableEq (PaddedBasis s n) := Classical.decEq _

def paddedWeights {d r : ℕ} (s : FixedSpectrum d r) (hd : 2 ≤ d) (n : ℕ) :
    GeometricOrbit.WeightData (PaddedBasis s n) (d.choose 2) s.qx :=
  weights s hd _ (targetIntegerRow_dominant s n)

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [MeasurableSpace G] [BorelSpace G]

/-- Average error of the actual matrix channels on the padded GT orbit. -/
def paddedOrbitError {d r : ℕ} (s : FixedSpectrum d r) (hd : 2 ≤ d) (n : ℕ)
    (haar : Measure G) (U : G →* Matrix (PaddedBasis s n) (PaddedBasis s n) ℂ)
    {M : Type*} [Fintype M] [DecidableEq M]
    (E : Channels.MatrixChannel (PaddedBasis s n) M)
    (D : Channels.MatrixChannel M (PaddedBasis s n)) : ℝ :=
  ∫ g, traceDistance (D.toFun (E.toFun
    (U g * (paddedWeights s hd n).state * (U g)ᴴ)))
    (U g * (paddedWeights s hd n).state * (U g)ᴴ) ∂haar

/-- Finite memory bound with the exact active Weyl product, proved from
the actual GT cardinality and the actual irreducible orbit bound. -/
theorem padded_memory_bound {d r : ℕ} (s : FixedSpectrum d r) (hd : 2 ≤ d) (n : ℕ)
    (haar : Measure G) [Measure.IsMulLeftInvariant haar] [IsProbabilityMeasure haar]
    (U : G →* Matrix (PaddedBasis s n) (PaddedBasis s n) ℂ) (hU : Continuous U)
    (hunitary : ∀ g, (U g)ᴴ * U g = 1)
    [Representation.IsIrreducible (matrixRepresentation U)]
    {M : Type*} [Fintype M] [DecidableEq M]
    (E : Channels.MatrixChannel (PaddedBasis s n) M)
    (D : Channels.MatrixChannel M (PaddedBasis s n)) :
    Weyl.activeProduct d r (s.targetRow n) *
      (1 - paddedOrbitError s hd n haar U E D / s.gammaX) ≤ (Fintype.card M : ℝ) := by
  rw [← targetDimension_weyl]
  exact memory_bound_gammaX s hd _ (targetIntegerRow_dominant s n) haar U hU hunitary E D

/-- The exact qmdl converse for actual padded GT orbit codes. The error is
the trace-distance error of the given channels; every dimension and spectral
estimate has been proved. A supplied genuine irreducible unitary action is
still needed to relate this model to the polynomial representation. -/
theorem theorem1_padded_orbit_converse {d r : ℕ} (s : FixedSpectrum d r) (hd : 2 ≤ d)
    (memory : ℕ → ℕ)
    (haar : Measure G) [Measure.IsMulLeftInvariant haar] [IsProbabilityMeasure haar]
    (U : ∀ n, G →* Matrix (PaddedBasis s n) (PaddedBasis s n) ℂ)
    (hU : ∀ n, Continuous (U n))
    (hunitary : ∀ n g, (U n g)ᴴ * U n g = 1)
    (hirrep : ∀ n, Representation.IsIrreducible (matrixRepresentation (U n)))
    (E : ∀ n, Channels.MatrixChannel (PaddedBasis s n) (Fin (memory n)))
    (D : ∀ n, Channels.MatrixChannel (Fin (memory n)) (PaddedBasis s n))
    (herror : Tendsto (fun n => paddedOrbitError s hd n haar (U n) (E n) (D n))
      atTop (𝓝 0)) :
    (0 : EReal) ≤ liminf
      (fun n => ((Real.logb 2 (memory n) - Weyl.qmdl d r s.eigenvalue n : ℝ) : EReal))
      atTop := by
  apply theorem1_converse_of_quantum_estimates s memory (targetDimension s)
    (fun n => paddedOrbitError s hd n haar (U n) (E n) (D n)) (fun _ => 0) s.gammaX
    (Eventually.of_forall (targetDimension_weyl s)) (targetDimension_pos s)
    s.gammaX_pos herror (Asymptotics.isBigO_zero _ _) ?_
  apply Eventually.of_forall
  intro n
  letI := hirrep n
  simpa only [add_zero, targetDimension_weyl, Fintype.card_fin] using
    padded_memory_bound s hd n haar (U n) (hU n) (hunitary n) (E n) (D n)

end FreeEntropy.GTOrbit
