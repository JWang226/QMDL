/-
Copyright (c) 2026 Free Entropy formalization contributors.
See LICENSE and NOTICE in the repository root for license and attribution.
-/

import FreeEntropy.SectorChannels
import FreeEntropy.QuantumProtocol

/-!
# Actual sector compression with the typical-sector error estimate

The encoder and decoder are constructed CPTP maps. Their formulas are
proved from the sector embeddings, so only the individual sector errors
and the probability outside the typical set remain in the final estimate.
-/

noncomputable section
open scoped BigOperators MatrixOrder ComplexOrder
open Matrix

namespace FreeEntropy.SectorProtocol
open Channels SectorChannels CloningMatrices TraceDistance

set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false

variable {ι S M : Type*} [Fintype ι] [Fintype S] [Fintype M]
  [DecidableEq ι] [DecidableEq S] [DecidableEq M]
variable {B : ι → Type*} [∀ i, Fintype (B i)] [∀ i, DecidableEq (B i)]

/-- The exact average of the two sector errors bounds the error of the
constructed source encoder and independently resampling decoder. -/
theorem sector_roundtrip_error (J : ∀ i, Matrix S (B i) ℂ)
    (F : ∀ i, MatrixChannel (B i) M) (G : ∀ i, MatrixChannel M (B i))
    (hresolve : ∑ i, J i * (J i)ᴴ = 1) (hJ : ∀ i, (J i)ᴴ * J i = 1)
    (horth : ∀ i j, i ≠ j → (J i)ᴴ * J j = 0)
    (q : ι → ℝ) (hq0 : ∀ i, 0 ≤ q i) (hq1 : ∑ i, q i = 1)
    (σ : ∀ i, Matrix (B i) (B i) ℂ) (hσ : ∀ i, (σ i).PosSemidef)
    (τ : Matrix M M ℂ) (hτ : τ.PosSemidef) :
    traceDistance ((decoder J G q hJ hq0 hq1).toFun
      ((encoder J F hresolve).toFun (∑ i, q i • embed (J i) (σ i))))
      (∑ i, q i • embed (J i) (σ i)) ≤
      (∑ i, q i * traceDistance ((F i).toFun (σ i)) τ) +
        ∑ i, q i * traceDistance ((G i).toFun τ) (σ i) := by
  have h := QuantumProtocol.mixture_roundtrip_error Finset.univ q
    (encoder J F hresolve) (decoder J G q hJ hq0 hq1)
    (fun i => embed (J i) (σ i)) (fun i => embed (J i) ((G i).toFun τ))
    (fun i => (F i).toFun (σ i)) τ (fun i _ => hq0 i) hq1
    (fun i _ => embed_positive (J i) (hσ i))
    (fun i _ => (F i).positive _ (hσ i))
    (fun i _ => embed_positive (J i) ((G i).positive _ hτ)) hτ
    (encoder_block_mixture J F hresolve hJ horth q σ) rfl
  have hrev (i : ι) : traceDistance (embed (J i) ((G i).toFun τ))
      (embed (J i) (σ i)) = traceDistance ((G i).toFun τ) (σ i) :=
    traceDistance_isometry (J i) (hJ i) ((G i).positive _ hτ) (hσ i)
  simpa only [mixture, hrev] using h

/-- The actual finite compression theorem. All aggregate error assumptions
have been replaced by two per-sector trace-distance bounds on the typical set. -/
theorem typical_sector_roundtrip_error (J : ∀ i, Matrix S (B i) ℂ)
    (F : ∀ i, MatrixChannel (B i) M) (G : ∀ i, MatrixChannel M (B i))
    (hresolve : ∑ i, J i * (J i)ᴴ = 1) (hJ : ∀ i, (J i)ᴴ * J i = 1)
    (horth : ∀ i j, i ≠ j → (J i)ᴴ * J j = 0)
    (q : ι → ℝ) (hq0 : ∀ i, 0 ≤ q i) (hq1 : ∑ i, q i = 1)
    (σ : ∀ i, Matrix (B i) (B i) ℂ) (hσ : ∀ i, (σ i).PosSemidef)
    (htσ : ∀ i, (σ i).trace = 1) (τ : Matrix M M ℂ)
    (hτ : τ.PosSemidef) (htτ : τ.trace = 1)
    (typical : Finset ι) (ε : ℝ) (hε : 0 ≤ ε)
    (hf : ∀ i ∈ typical, traceDistance ((F i).toFun (σ i)) τ ≤ ε)
    (hr : ∀ i ∈ typical, traceDistance ((G i).toFun τ) (σ i) ≤ ε) :
    traceDistance ((decoder J G q hJ hq0 hq1).toFun
      ((encoder J F hresolve).toFun (∑ i, q i • embed (J i) (σ i))))
      (∑ i, q i • embed (J i) (σ i)) ≤
      2 * ε + 2 * Protocol.outsideMass Finset.univ typical q := by
  apply Protocol.roundtrip_error_le Finset.univ typical q
    (fun i => traceDistance ((F i).toFun (σ i)) τ)
    (fun i => traceDistance ((G i).toFun τ) (σ i)) ε _
    (fun i _ => hq0 i) hq1 hε (fun i _ hi => hf i hi) (fun i _ hi => hr i hi)
  · intro i _
    exact traceDistance_states_le_one ((F i).positive _ (hσ i)) hτ
      (((F i).trace_preserving _).trans (htσ i)) htτ
  · intro i _
    exact traceDistance_states_le_one ((G i).positive _ hτ) (hσ i)
      (((G i).trace_preserving _).trans htτ) (htσ i)
  · exact sector_roundtrip_error J F G hresolve hJ horth q hq0 hq1 σ hσ τ hτ

/-- The source matrix on the actual dependent direct sum of sectors. -/
def directSumState (q : ι → ℝ) (σ : ∀ i, Matrix (B i) (B i) ℂ) :
    Matrix (Σ i, B i) (Σ i, B i) ℂ :=
  ∑ i, q i • embed (sectorEmbedding i) (σ i)

theorem directSumState_positive (q : ι → ℝ) (hq : ∀ i, 0 ≤ q i)
    (σ : ∀ i, Matrix (B i) (B i) ℂ) (hσ : ∀ i, (σ i).PosSemidef) :
    (directSumState q σ).PosSemidef := by
  exact Matrix.posSemidef_sum _ (fun i _ =>
    (embed_positive (sectorEmbedding i) (hσ i)).smul (hq i))

theorem directSumState_trace (q : ι → ℝ) (hq : ∑ i, q i = 1)
    (σ : ∀ i, Matrix (B i) (B i) ℂ) (hσ : ∀ i, (σ i).trace = 1) :
    (directSumState q σ).trace = 1 := by
  simp only [directSumState, Matrix.trace_sum, Matrix.trace_smul,
    trace_embed _ (sectorEmbedding_isometry _), hσ]
  rw [← Finset.sum_smul, hq, one_smul]

/-- Canonical direct-sum form of the finite compression theorem. Even the
sector embeddings and their orthogonality are constructed, not assumed. -/
theorem directSum_typical_roundtrip_error
    (F : ∀ i, MatrixChannel (B i) M) (G : ∀ i, MatrixChannel M (B i))
    (q : ι → ℝ) (hq0 : ∀ i, 0 ≤ q i) (hq1 : ∑ i, q i = 1)
    (σ : ∀ i, Matrix (B i) (B i) ℂ) (hσ : ∀ i, (σ i).PosSemidef)
    (htσ : ∀ i, (σ i).trace = 1) (τ : Matrix M M ℂ)
    (hτ : τ.PosSemidef) (htτ : τ.trace = 1)
    (typical : Finset ι) (ε : ℝ) (hε : 0 ≤ ε)
    (hf : ∀ i ∈ typical, traceDistance ((F i).toFun (σ i)) τ ≤ ε)
    (hr : ∀ i ∈ typical, traceDistance ((G i).toFun τ) (σ i) ≤ ε) :
    traceDistance ((directSumDecoder G q hq0 hq1).toFun
      ((directSumEncoder F).toFun (directSumState q σ))) (directSumState q σ) ≤
      2 * ε + 2 * Protocol.outsideMass Finset.univ typical q :=
  typical_sector_roundtrip_error sectorEmbedding F G sectorEmbedding_resolution
    sectorEmbedding_isometry sectorEmbedding_orthogonal q hq0 hq1 σ hσ htσ τ hτ htτ
    typical ε hε hf hr

end FreeEntropy.SectorProtocol
