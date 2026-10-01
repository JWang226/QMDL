/-
Copyright (c) 2026 Free Entropy formalization contributors.
See LICENSE and NOTICE in the repository root for license and attribution.
-/

import FreeEntropy.GTPartitions
import FreeEntropy.KostantWeightData
import FreeEntropy.SpectrumBounds
import FreeEntropy.QuantumTransfer
import FreeEntropy.RootPartitionFunction

/-!
# Concrete GT orbit states

The Hilbert basis consists of all integral GT patterns in ambient dimension
`d`, even when the spectrum has smaller rank `r`. The root-partition injection
constructs every counting/envelope field and proves a uniform spectral gap.
Identifying this explicit diagonal state and a supplied irreducible unitary
representation with the manuscript's polynomial representation remains a
separate representation-theoretic task.
-/

noncomputable section
open scoped BigOperators Matrix.Norms.Elementwise Topology
open Matrix MeasureTheory Filter
open FreeEntropy.GelfandTsetlin FreeEntropy.KostantCounting
open FreeEntropy.OrbitMemory FreeEntropy.TraceDistance FreeEntropy.Twirling

namespace FreeEntropy.GeometricOrbit

/-- Transport concrete weight data along a genuine bijection of its basis. -/
def WeightData.reindex {H K : Type*} [Fintype H] [Fintype K]
    {N : ℕ} {q : ℝ} (W : WeightData H N q) (e : K ≃ H) : WeightData K N q where
  weight k := W.weight (e k)
  depth k := W.depth (e k)
  highest := e.symm W.highest
  nonneg k := W.nonneg (e k)
  highest_weight := by simpa using W.highest_weight
  other_depth k hk := W.other_depth (e k) (by
    intro he
    exact hk (e.injective (by simpa using he)))
  envelope k := W.envelope (e k)
  count t := by
    classical
    have he := Equiv.sum_comp e (fun h => if W.depth h = t then (1 : ℕ) else 0)
    have hc := W.count t
    simp only [Finset.sum_filter] at hc ⊢
    exact he.trans_le hc

end FreeEntropy.GeometricOrbit

namespace FreeEntropy.GTOrbit

variable {d r : ℕ}
local instance {μ : Fin d → ℤ} : DecidableEq (Pattern μ) := Classical.decEq _

theorem adjacentRatio_le_qx (s : FixedSpectrum d r) (i : ℕ) :
    s.adjacentRatio i ≤ s.qx := by
  by_cases hi : i + 1 < r
  · simpa only [FixedSpectrum.adjacentRatio, hi, ↓reduceIte] using s.adjacent_ratio_le_qx i hi
  · simpa only [FixedSpectrum.adjacentRatio, hi, ↓reduceIte] using s.qx_nonneg

/-- Explicit normalized weight model in the full ambient GT basis. -/
def weights (s : FixedSpectrum d r) (hd : 2 ≤ d)
    (μ : Fin d → ℤ) (hμ : Dominant μ) :
    GeometricOrbit.WeightData (Pattern μ) (d.choose 2) s.qx :=
  KostantWeightData.ofRootEncoding d hd s.qx drops drops_injective drops_support
    (highestPattern μ hμ) (drops_highestPattern μ hμ) s.adjacentRatio
    (fun j _ => s.adjacentRatio_nonneg j) (fun j _ => adjacentRatio_le_qx s j)

/-- The same state data enumerated by `Fin`, without changing dimension. -/
def finiteWeights (s : FixedSpectrum d r) (hd : 2 ≤ d)
    (μ : Fin d → ℤ) (hμ : Dominant μ) :
    GeometricOrbit.WeightData (Fin (Fintype.card (Pattern μ))) (d.choose 2) s.qx :=
  (weights s hd μ hμ).reindex (Fintype.equivFin (Pattern μ)).symm

theorem pattern_card_pos (μ : Fin d → ℤ) (hμ : Dominant μ) :
    0 < Fintype.card (Pattern μ) := by
  letI : Nonempty (Pattern μ) := ⟨highestPattern μ hμ⟩
  exact Fintype.card_pos

theorem uniform_gap (s : FixedSpectrum d r) (hd : 2 ≤ d)
    (μ : Fin d → ℤ) (hμ : Dominant μ) :
    0 < (1 - s.qx) ^ (d.choose 2 + 1) ∧
      (1 - s.qx) ^ (d.choose 2 + 1) ≤
        1 / (weights s hd μ hμ).normalizer -
          s.qx * (1 / (weights s hd μ hμ).normalizer) :=
  (weights s hd μ hμ).gap_lower (Nat.choose_pos hd) s.qx_nonneg s.qx_lt_one

/-- The exact top-eigenvalue lower bound in the paper, now proved for
all ambient GT patterns and including rank-deficient spectra. -/
theorem top_lower (s : FixedSpectrum d r) (hd : 2 ≤ d)
    (μ : Fin d → ℤ) (hμ : Dominant μ) :
    s.spectralProduct ≤ 1 / (weights s hd μ hμ).normalizer :=
  RootPartitionFunction.weightData_top_lower s (weights s hd μ hμ)
    drops drops_injective drops_support (fun _ => rfl) (drops_highestPattern μ hμ)

theorem exact_gap (s : FixedSpectrum d r) (hd : 2 ≤ d)
    (μ : Fin d → ℤ) (hμ : Dominant μ) :
    s.gammaX ≤ 1 / (weights s hd μ hμ).normalizer -
      s.qx * (1 / (weights s hd μ hμ).normalizer) :=
  s.gammaX_le_eigenvalue_gap (top_lower s hd μ hμ) le_rfl

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [MeasurableSpace G] [BorelSpace G]

/-- Actual matrix-channel memory bound for the explicit GT diagonal state.
All spectral and multiplicity estimates have been proved by construction. -/
theorem memory_bound (s : FixedSpectrum d r) (hd : 2 ≤ d)
    (μ : Fin d → ℤ) (hμ : Dominant μ)
    (haar : Measure G) [Measure.IsMulLeftInvariant haar] [IsProbabilityMeasure haar]
    (U : G →* Matrix (Pattern μ) (Pattern μ) ℂ) (hU : Continuous U)
    (hunitary : ∀ g, (U g)ᴴ * U g = 1)
    [Representation.IsIrreducible (matrixRepresentation U)]
    {M : Type*} [Fintype M] [DecidableEq M]
    (E : Channels.MatrixChannel (Pattern μ) M) (D : Channels.MatrixChannel M (Pattern μ)) :
    (Fintype.card (Pattern μ) : ℝ) * (1 -
      (∫ g, traceDistance (D.toFun (E.toFun
        (U g * (weights s hd μ hμ).state * (U g)ᴴ)))
        (U g * (weights s hd μ hμ).state * (U g)ᴴ) ∂haar) /
        (1 - s.qx) ^ (d.choose 2 + 1)) ≤ (Fintype.card M : ℝ) :=
  GeometricOrbit.memory_bound haar (weights s hd μ hμ) (Nat.choose_pos hd)
    s.qx_nonneg s.qx_lt_one U hU hunitary E D

/-- The finite GT-orbit converse with the exact constant `gammaX` from
the manuscript. No spectral, counting, or normalized-weight hypotheses remain. -/
theorem memory_bound_gammaX (s : FixedSpectrum d r) (hd : 2 ≤ d)
    (μ : Fin d → ℤ) (hμ : Dominant μ)
    (haar : Measure G) [Measure.IsMulLeftInvariant haar] [IsProbabilityMeasure haar]
    (U : G →* Matrix (Pattern μ) (Pattern μ) ℂ) (hU : Continuous U)
    (hunitary : ∀ g, (U g)ᴴ * U g = 1)
    [Representation.IsIrreducible (matrixRepresentation U)]
    {M : Type*} [Fintype M] [DecidableEq M]
    (E : Channels.MatrixChannel (Pattern μ) M) (D : Channels.MatrixChannel M (Pattern μ)) :
    (Fintype.card (Pattern μ) : ℝ) * (1 -
      (∫ g, traceDistance (D.toFun (E.toFun
        (U g * (weights s hd μ hμ).state * (U g)ᴴ)))
        (U g * (weights s hd μ hμ).state * (U g)ᴴ) ∂haar) / s.gammaX) ≤
        (Fintype.card M : ℝ) :=
  RootPartitionFunction.weightData_memory_bound_gammaX s haar (weights s hd μ hμ)
    drops drops_injective drops_support (fun _ => rfl) (drops_highestPattern μ hμ)
    U hU hunitary E D

end FreeEntropy.GTOrbit
