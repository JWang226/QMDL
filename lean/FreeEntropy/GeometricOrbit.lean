/-
Copyright (c) 2026 Free Entropy formalization contributors.
See LICENSE and NOTICE in the repository root for license and attribution.
-/

import FreeEntropy.WeightNormalization
import FreeEntropy.OrbitTraceDistance
import FreeEntropy.SpectralProjector

/-!
# Orbit converse with a spectral gap derived from weight counting

A finite weight basis and its geometric depth envelope define the state.
The negative-binomial multiplicity bound proves a uniform gap
`(1-q)^(N+1)`. This positive constant is sufficient for the exact asymptotic
memory lower bound, so no separate highest-eigenvalue product estimate is
needed on this route.
-/

noncomputable section
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.Elementwise Topology
open Matrix MeasureTheory MeasureTheory.Measure Filter
open FreeEntropy.OrbitMemory FreeEntropy.TraceDistance FreeEntropy.Twirling
open FreeEntropy.WeightNormalization FreeEntropy.SpectralProjector

namespace FreeEntropy.GeometricOrbit
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 400000

/-- Concrete weight-basis data. The count is over basis vectors, so weight
multiplicities are included automatically. -/
structure WeightData (H : Type*) [Fintype H] (N : ℕ) (q : ℝ) where
  weight : H → ℝ
  depth : H → ℕ
  highest : H
  nonneg : ∀ i, 0 ≤ weight i
  highest_weight : weight highest = 1
  other_depth : ∀ i, i ≠ highest → 1 ≤ depth i
  envelope : ∀ i, weight i ≤ q ^ depth i
  count : ∀ t, ∑ i ∈ Finset.univ with depth i = t, (1 : ℕ) ≤
    (t + N - 1).choose (N - 1)

variable {H M : Type*} [Fintype H] [DecidableEq H] [Fintype M] [DecidableEq M]
variable {N : ℕ} {q : ℝ}

def WeightData.normalizer (W : WeightData H N q) : ℝ :=
  partitionFunction Finset.univ (fun _ => 1) W.weight

def WeightData.state (W : WeightData H N q) : Matrix H H ℂ :=
  Matrix.diagonal (fun i => ((W.weight i / W.normalizer : ℝ) : ℂ))

theorem WeightData.normalizer_ge_one (W : WeightData H N q) : 1 ≤ W.normalizer :=
  partitionFunction_ge_one _ _ _ (fun i _ => W.nonneg i) W.highest
    (Finset.mem_univ _) rfl W.highest_weight

theorem WeightData.normalizer_pos (W : WeightData H N q) : 0 < W.normalizer :=
  lt_of_lt_of_le zero_lt_one W.normalizer_ge_one

theorem WeightData.state_positive (W : WeightData H N q) : W.state.PosSemidef := by
  apply Matrix.PosSemidef.diagonal
  intro i
  exact Complex.zero_le_real.mpr (div_nonneg (W.nonneg i) W.normalizer_pos.le)

theorem WeightData.state_trace (W : WeightData H N q) : W.state.trace = 1 := by
  have hs := coefficient_normalized Finset.univ (fun _ : H => 1) W.weight W.normalizer_pos.ne'
  simp only [coefficient, Nat.cast_one, mul_one] at hs
  rw [WeightData.state, Matrix.trace_diagonal]
  change (∑ i, ((W.weight i / W.normalizer : ℝ) : ℂ)) = 1
  rw [← Complex.ofReal_sum]
  exact_mod_cast hs

theorem WeightData.normalizer_upper (W : WeightData H N q)
    (hN : 0 < N) (hq : 0 ≤ q) (hq1 : q < 1) :
    W.normalizer ≤ 1 / (1 - q) ^ N :=
  partitionFunction_le _ W.depth (fun _ => 1) W.weight N hN q hq hq1
    (fun i _ => W.envelope i) W.count

theorem WeightData.next_upper (W : WeightData H N q) (hq : 0 ≤ q) (hq1 : q ≤ 1)
    (i : H) (hi : i ≠ W.highest) :
    W.weight i / W.normalizer ≤ q * (1 / W.normalizer) :=
  next_coefficient_upper _ W.depth (fun _ => 1) W.weight q hq hq1 W.normalizer_pos
    i (W.other_depth i hi) (W.envelope i)

theorem WeightData.peak_overlap (W : WeightData H N q) :
    tr (coordinateProjection W.highest * W.state) = 1 / W.normalizer := by
  simp [coordinateProjection, WeightData.state, Matrix.diagonal_mul_diagonal,
    tr, W.highest_weight]

theorem WeightData.spectral_upper (W : WeightData H N q) (hq : 0 ≤ q) (hq1 : q ≤ 1) :
    W.state ≤ (q * (1 / W.normalizer)) • (1 : Matrix H H ℂ) +
      (1 / W.normalizer - q * (1 / W.normalizer)) • coordinateProjection W.highest := by
  apply Matrix.le_iff.mpr
  have hid : (q * (1 / W.normalizer)) • (1 : Matrix H H ℂ) +
      (1 / W.normalizer - q * (1 / W.normalizer)) • coordinateProjection W.highest - W.state =
      Matrix.diagonal (fun i => (((if i = W.highest then 1 / W.normalizer
        else q * (1 / W.normalizer)) - W.weight i / W.normalizer : ℝ) : ℂ)) := by
    ext i j
    by_cases hij : i = j
    · subst j
      by_cases hi : i = W.highest <;>
        simp [coordinateProjection, WeightData.state, Matrix.smul_apply, hi,
          Complex.real_smul, Complex.ofReal_sub]
    · simp [coordinateProjection, WeightData.state, Matrix.smul_apply, hij]
  rw [hid]
  apply Matrix.PosSemidef.diagonal
  intro i
  apply Complex.zero_le_real.mpr
  by_cases hi : i = W.highest
  · simp [hi, W.highest_weight]
  · simpa [hi] using sub_nonneg.mpr (W.next_upper hq hq1 i hi)

theorem WeightData.gap_lower (W : WeightData H N q)
    (hN : 0 < N) (hq : 0 ≤ q) (hq1 : q < 1) :
    0 < (1 - q) ^ (N + 1) ∧ (1 - q) ^ (N + 1) ≤
      1 / W.normalizer - q * (1 / W.normalizer) :=
  uniform_gap _ (fun _ => 1) W.weight N q hq1 W.normalizer_pos
    (W.normalizer_upper hN hq hq1)

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [MeasurableSpace G] [BorelSpace G]

/-- The finite memory bound now derives its uniform spectral gap entirely
from concrete normalized weight data. -/
theorem memory_bound (μ : Measure G) [IsMulLeftInvariant μ] [IsProbabilityMeasure μ]
    (W : WeightData H N q) (hN : 0 < N) (hq : 0 ≤ q) (hq1 : q < 1)
    (U : G →* Matrix H H ℂ) (hU : Continuous U)
    (hunitary : ∀ g, (U g)ᴴ * U g = 1)
    [Representation.IsIrreducible (matrixRepresentation U)]
    (E : Channels.MatrixChannel H M) (D : Channels.MatrixChannel M H) :
    (Fintype.card H : ℝ) * (1 -
      (∫ g, traceDistance (D.toFun (E.toFun (U g * W.state * (U g)ᴴ)))
        (U g * W.state * (U g)ᴴ) ∂μ) / (1 - q) ^ (N + 1)) ≤ (Fintype.card M : ℝ) := by
  letI : Nonempty H := ⟨W.highest⟩
  obtain ⟨hγ, hgap⟩ := W.gap_lower hN hq hq1
  have h := OrbitTraceDistance.irreducible_orbit_memory_bound μ U hU hunitary
    E.toRealLinearMap D.toRealLinearMap E.positive D.positive E.trace_preserving D.trace_preserving
    (coordinateProjection W.highest) W.state (coordinateProjection_pos _)
    (coordinateProjection_trace _) W.state_positive (hγ.trans_le hgap)
    W.peak_overlap (W.spectral_upper hq hq1.le)
  have hδ : 0 ≤ ∫ g, traceDistance (D.toFun (E.toFun (U g * W.state * (U g)ᴴ)))
      (U g * W.state * (U g)ᴴ) ∂μ := integral_nonneg (fun _ => traceDistance_nonneg _ _)
  have hdiv := div_le_div_of_nonneg_left hδ hγ hgap
  have hcoef : 1 - (∫ g, traceDistance (D.toFun (E.toFun (U g * W.state * (U g)ᴴ)))
      (U g * W.state * (U g)ᴴ) ∂μ) / (1 - q) ^ (N + 1) ≤
      1 - (∫ g, traceDistance (D.toFun (E.toFun (U g * W.state * (U g)ᴴ)))
      (U g * W.state * (U g)ᴴ) ∂μ) /
        (1 / W.normalizer - q * (1 / W.normalizer)) := by linarith
  exact (mul_le_mul_of_nonneg_left hcoef (Nat.cast_nonneg _)).trans h

/-- An actual finite-dimensional orbit code whose state and spectral gap
are both constructed from its weight basis. -/
structure Code (N : ℕ) (q : ℝ) (G : Type*) [Group G] [TopologicalSpace G]
    (target memory : ℕ) where
  weights : WeightData (Fin target) N q
  U : G →* Matrix (Fin target) (Fin target) ℂ
  continuous_U : Continuous U
  unitary : ∀ g, (U g)ᴴ * U g = 1
  irreducible : Representation.IsIrreducible (matrixRepresentation U)
  encoder : Channels.MatrixChannel (Fin target) (Fin memory)
  decoder : Channels.MatrixChannel (Fin memory) (Fin target)

def Code.averageError {target memory : ℕ} (C : Code N q G target memory) (μ : Measure G) : ℝ :=
  ∫ g, traceDistance (C.decoder.toFun (C.encoder.toFun
    (C.U g * C.weights.state * (C.U g)ᴴ))) (C.U g * C.weights.state * (C.U g)ᴴ) ∂μ

theorem Code.memory_bound {target memory : ℕ} (C : Code N q G target memory)
    (μ : Measure G) [IsMulLeftInvariant μ] [IsProbabilityMeasure μ]
    (hN : 0 < N) (hq : 0 ≤ q) (hq1 : q < 1) :
    (target : ℝ) * (1 - C.averageError μ / (1 - q) ^ (N + 1)) ≤ (memory : ℝ) := by
  letI := C.irreducible
  simpa only [Code.averageError, Fintype.card_fin] using
    FreeEntropy.GeometricOrbit.memory_bound μ C.weights hN hq hq1 C.U C.continuous_U C.unitary C.encoder C.decoder

/-- Theorem 1 converse with the uniform gap derived from actual weight
normalizers and a combinatorial count. No spectral product bound, matrix
spectral inequality, or scalar memory lower bound is assumed. -/
theorem theorem1_converse_of_weight_codes {d r : ℕ} (s : FixedSpectrum d r)
    (N : ℕ) (q : ℝ) (hN : 0 < N) (hq : 0 ≤ q) (hq1 : q < 1)
    (memory target : ℕ → ℕ) (δ e : ℕ → ℝ)
    (μ : Measure G) [IsMulLeftInvariant μ] [IsProbabilityMeasure μ]
    (C : ∀ n, Code N q G (target n) (memory n))
    (hdim : ∀ᶠ n in atTop, (target n : ℝ) = Weyl.activeProduct d r (s.targetRow n))
    (htarget : ∀ n, 0 < target n)
    (hδ : Tendsto δ atTop (𝓝 0)) (he : Asymptotics.IsBigO atTop e Weyl.errorScale)
    (herror : ∀ᶠ n in atTop, (C n).averageError μ ≤ δ n + e n) :
    (0 : EReal) ≤ liminf
      (fun n => ((Real.logb 2 (memory n) - Weyl.qmdl d r s.eigenvalue n : ℝ) : EReal)) atTop := by
  have hγ : 0 < (1 - q) ^ (N + 1) := pow_pos (by linarith) _
  apply theorem1_converse_of_quantum_estimates s memory target δ e ((1 - q) ^ (N + 1))
    hdim htarget hγ hδ he
  filter_upwards [herror] with n hn
  have hm := (C n).memory_bound μ hN hq hq1
  have hr := div_le_div_of_nonneg_right hn hγ.le
  have hc : 1 - (δ n + e n) / (1 - q) ^ (N + 1) ≤
      1 - (C n).averageError μ / (1 - q) ^ (N + 1) := by linarith
  exact (mul_le_mul_of_nonneg_left hc (Nat.cast_nonneg (target n))).trans hm

end FreeEntropy.GeometricOrbit
