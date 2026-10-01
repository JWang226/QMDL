/-
Copyright (c) 2026 Free Entropy formalization contributors.
See LICENSE and NOTICE in the repository root for license and attribution.
-/

import FreeEntropy.PhysicalSchurProtocol

/-! Separate source-to-target and target-to-source errors for the actual
physical maps. Both bounds use the derived physical concentration tail. -/
noncomputable section
open Matrix
open scoped BigOperators MatrixOrder ComplexOrder
namespace FreeEntropy.SchurWeyl
open Channels TraceDistance SectorChannels
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
variable {d r : ℕ} {M : Type*} [Fintype M] [DecidableEq M]

theorem physicalEncoder_source (s : FixedSpectrum d r) (n : ℕ)
    (F : ∀ i : Sector d n, MatrixChannel (SectorSpace d n i) M)
    (U : Matrix.unitaryGroup (Fin d) ℂ) :
    (physicalEncoder F).toFun (TensorPowers.matrix n (physicalDensity s U)) =
      ∑ i : Sector d n, physicalProbability s n i • (F i).toFun (physicalSectorState s n U i) := by
  rw [physical_source_mixture]
  exact encoder_block_mixture (physicalDecomposition d n).embedding F
    (physicalDecomposition d n).resolution (physicalDecomposition d n).isometry
    (physicalDecomposition d n).orthogonal (physicalProbability s n) (physicalSectorState s n U)

/-- Each direction needs only one copy of the actual atypical mass. -/
theorem physical_forward_error_le (s : FixedSpectrum d r) (n : ℕ) (hn : 2 ≤ n)
    (F : ∀ i : Sector d n, MatrixChannel (SectorSpace d n i) M)
    (U : Matrix.unitaryGroup (Fin d) ℂ) (τ : Matrix M M ℂ)
    (hτ : τ.PosSemidef) (hτ1 : τ.trace = 1) (ε : ℝ) (hε : 0 ≤ ε)
    (hf : ∀ i ∈ physicalTypical s n,
      traceDistance ((F i).toFun (physicalSectorState s n U i)) τ ≤ ε) :
    traceDistance ((physicalEncoder F).toFun (TensorPowers.matrix n (physicalDensity s U))) τ ≤
      ε + Concentration.tailBound (concentrationExponent d + d) n := by
  have hc := traceDistance_mixture_le Finset.univ (physicalProbability s n)
    (fun i => (F i).toFun (physicalSectorState s n U i)) τ
    (fun i _ => physicalProbability_nonneg s n i) (physicalProbability_sum s n)
    (fun i _ => ((F i).positive _ (physicalSectorState_positive s n U i)).isHermitian) hτ.isHermitian
  have hb := Protocol.weighted_error_le Finset.univ (physicalTypical s n) (physicalProbability s n)
    (fun i => traceDistance ((F i).toFun (physicalSectorState s n U i)) τ) ε
    (fun i _ => physicalProbability_nonneg s n i) (physicalProbability_sum s n) hε
    (fun i _ hi => hf i hi)
    (fun i _ => traceDistance_states_le_one ((F i).positive _ (physicalSectorState_positive s n U i)) hτ
      (((F i).trace_preserving _).trans (physicalSectorState_trace s n U i)) hτ1)
  rw [physical_outsideMass] at hb
  rw [physicalEncoder_source]
  exact hc.trans (hb.trans (by linarith [physicalAtypicalMass_le_tailBound s n hn]))

theorem physical_reverse_error_le (s : FixedSpectrum d r) (n : ℕ) (hn : 2 ≤ n)
    (G : ∀ i : Sector d n, MatrixChannel M (SectorSpace d n i))
    (U : Matrix.unitaryGroup (Fin d) ℂ) (τ : Matrix M M ℂ)
    (hτ : τ.PosSemidef) (hτ1 : τ.trace = 1) (ε : ℝ) (hε : 0 ≤ ε)
    (hr : ∀ i ∈ physicalTypical s n,
      traceDistance ((G i).toFun τ) (physicalSectorState s n U i) ≤ ε) :
    traceDistance ((physicalDecoder s n G).toFun τ) (TensorPowers.matrix n (physicalDensity s U)) ≤
      ε + Concentration.tailBound (concentrationExponent d + d) n := by
  have hc := traceDistance_mixtures_le Finset.univ (physicalProbability s n)
    (fun i => embed ((physicalDecomposition d n).embedding i) ((G i).toFun τ))
    (fun i => embed ((physicalDecomposition d n).embedding i) (physicalSectorState s n U i))
    (fun i _ => physicalProbability_nonneg s n i)
    (fun i _ => (embed_positive _ ((G i).positive _ hτ)).isHermitian)
    (fun i _ => (embed_positive _ (physicalSectorState_positive s n U i)).isHermitian)
  have hiso (i : Sector d n) : traceDistance
      (embed ((physicalDecomposition d n).embedding i) ((G i).toFun τ))
      (embed ((physicalDecomposition d n).embedding i) (physicalSectorState s n U i)) =
      traceDistance ((G i).toFun τ) (physicalSectorState s n U i) :=
    traceDistance_isometry _ ((physicalDecomposition d n).isometry i)
      ((G i).positive _ hτ) (physicalSectorState_positive s n U i)
  simp only [CloningMatrices.mixture, hiso] at hc
  rw [← physical_source_mixture] at hc
  have hb := Protocol.weighted_error_le Finset.univ (physicalTypical s n) (physicalProbability s n)
    (fun i => traceDistance ((G i).toFun τ) (physicalSectorState s n U i)) ε
    (fun i _ => physicalProbability_nonneg s n i) (physicalProbability_sum s n) hε
    (fun i _ hi => hr i hi)
    (fun i _ => traceDistance_states_le_one ((G i).positive _ hτ) (physicalSectorState_positive s n U i)
      (((G i).trace_preserving _).trans hτ1) (physicalSectorState_trace s n U i))
  rw [physical_outsideMass] at hb
  exact hc.trans (hb.trans (by linarith [physicalAtypicalMass_le_tailBound s n hn]))

end FreeEntropy.SchurWeyl
