/-
Copyright (c) 2026 Free Entropy formalization contributors.
See LICENSE and NOTICE in the repository root for license and attribution.
-/

import FreeEntropy.MultiplicityChannels
import FreeEntropy.SectorProtocol

/-!
# Concrete Schur-sector protocol with multiplicity registers

The source is the actual direct sum of irreducible sectors tensored with
maximally mixed multiplicity registers. The encoder discards each register;
the decoder restores it. This file constructs both CPTP maps and proves the
finite error estimate directly from the irreducible-sector errors. An
identification of this source with the manuscript's tensor-power state is
still representation-theoretic input.
-/

noncomputable section
open scoped BigOperators Matrix Kronecker ComplexOrder MatrixOrder
open Matrix

namespace FreeEntropy.SchurProtocol
open Channels MultiplicityChannels TraceDistance

set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false

variable {ι M : Type*} [Fintype ι] [Fintype M] [DecidableEq ι] [DecidableEq M]
variable {B A : ι → Type*} [∀ i, Fintype (B i)] [∀ i, DecidableEq (B i)]
  [∀ i, Fintype (A i)] [∀ i, DecidableEq (A i)] [∀ i, Nonempty (A i)]

def sectorEncoder (F : ∀ i, MatrixChannel (B i) M) (i : ι) :
    MatrixChannel (B i × A i) M := (F i).comp discardChannel

def sectorDecoder (G : ∀ i, MatrixChannel M (B i)) (i : ι) :
    MatrixChannel M (B i × A i) := appendChannel.comp (G i)

def encoder (F : ∀ i, MatrixChannel (B i) M) : MatrixChannel (Σ i, B i × A i) M :=
  SectorChannels.directSumEncoder (sectorEncoder (A := A) F)

def decoder (G : ∀ i, MatrixChannel M (B i)) (q : ι → ℝ)
    (hq0 : ∀ i, 0 ≤ q i) (hq1 : ∑ i, q i = 1) : MatrixChannel M (Σ i, B i × A i) :=
  SectorChannels.directSumDecoder (sectorDecoder (A := A) G) q hq0 hq1

/-- The block mixture including each maximally mixed multiplicity register. -/
def sourceState (q : ι → ℝ) (σ : ∀ i, Matrix (B i) (B i) ℂ) :
    Matrix (Σ i, B i × A i) (Σ i, B i × A i) ℂ :=
  SectorProtocol.directSumState q (fun i => appendMap (A := A i) (σ i))

theorem sourceState_positive (q : ι → ℝ) (hq : ∀ i, 0 ≤ q i)
    (σ : ∀ i, Matrix (B i) (B i) ℂ) (hσ : ∀ i, (σ i).PosSemidef) :
    (sourceState (A := A) q σ).PosSemidef :=
  SectorProtocol.directSumState_positive q hq _ (fun i => appendMap_positive (hσ i))

theorem sourceState_trace (q : ι → ℝ) (hq : ∑ i, q i = 1)
    (σ : ∀ i, Matrix (B i) (B i) ℂ) (hσ : ∀ i, (σ i).trace = 1) :
    (sourceState (A := A) q σ).trace = 1 :=
  SectorProtocol.directSumState_trace q hq _ (fun i => (appendMap_trace (σ i)).trans (hσ i))

theorem sectorEncoder_product (F : ∀ i, MatrixChannel (B i) M)
    (i : ι) (X : Matrix (B i) (B i) ℂ) :
    (sectorEncoder (A := A) F i).toFun (appendMap (A := A i) X) = (F i).toFun X := by
  change (F i).toFun (discardChannel.toFun (X ⊗ₖ maximallyMixed (A i))) = _
  rw [discard_product X (maximallyMixed (A i)) maximallyMixed_trace]

theorem sectorDecoder_apply (G : ∀ i, MatrixChannel M (B i))
    (i : ι) (Y : Matrix M M ℂ) :
    (sectorDecoder (A := A) G i).toFun Y = appendMap (A := A i) ((G i).toFun Y) :=
  appendChannel_apply _

/-- The error with multiplicity registers is exactly the irreducible-sector
reverse error; appending those registers introduces no additional loss. -/
theorem sectorDecoder_error (G : ∀ i, MatrixChannel M (B i)) (i : ι)
    {X : Matrix (B i) (B i) ℂ} {Y : Matrix M M ℂ}
    (hX : X.PosSemidef) (hY : Y.PosSemidef) :
    traceDistance ((sectorDecoder (A := A) G i).toFun Y) (appendMap (A := A i) X) =
      traceDistance ((G i).toFun Y) X := by
  rw [sectorDecoder_apply]
  exact traceDistance_append ((G i).positive _ hY) hX

theorem encoder_sourceState (F : ∀ i, MatrixChannel (B i) M)
    (q : ι → ℝ) (σ : ∀ i, Matrix (B i) (B i) ℂ) :
    (encoder (A := A) F).toFun (sourceState (A := A) q σ) =
      ∑ i, q i • (F i).toFun (σ i) := by
  have h := SectorChannels.encoder_block_mixture SectorChannels.sectorEmbedding
    (sectorEncoder (A := A) F) SectorChannels.sectorEmbedding_resolution
    SectorChannels.sectorEmbedding_isometry SectorChannels.sectorEmbedding_orthogonal
    q (fun i => appendMap (A := A i) (σ i))
  simpa only [encoder, sourceState, SectorChannels.directSumEncoder,
    SectorProtocol.directSumState, sectorEncoder_product] using h

/-- The concrete finite compression theorem including discarded/restored
multiplicity registers, using only irreducible-sector trace-distance errors. -/
theorem typical_roundtrip_error
    (F : ∀ i, MatrixChannel (B i) M) (G : ∀ i, MatrixChannel M (B i))
    (q : ι → ℝ) (hq0 : ∀ i, 0 ≤ q i) (hq1 : ∑ i, q i = 1)
    (σ : ∀ i, Matrix (B i) (B i) ℂ) (hσ : ∀ i, (σ i).PosSemidef)
    (htσ : ∀ i, (σ i).trace = 1) (τ : Matrix M M ℂ)
    (hτ : τ.PosSemidef) (htτ : τ.trace = 1)
    (typical : Finset ι) (ε : ℝ) (hε : 0 ≤ ε)
    (hf : ∀ i ∈ typical, traceDistance ((F i).toFun (σ i)) τ ≤ ε)
    (hr : ∀ i ∈ typical, traceDistance ((G i).toFun τ) (σ i) ≤ ε) :
    traceDistance ((decoder (A := A) G q hq0 hq1).toFun
      ((encoder (A := A) F).toFun (sourceState (A := A) q σ))) (sourceState (A := A) q σ) ≤
      2 * ε + 2 * Protocol.outsideMass Finset.univ typical q := by
  apply SectorProtocol.directSum_typical_roundtrip_error
    (sectorEncoder (A := A) F) (sectorDecoder (A := A) G) q hq0 hq1
    (fun i => appendMap (A := A i) (σ i)) (fun i => appendMap_positive (hσ i))
    (fun i => (appendMap_trace (σ i)).trans (htσ i)) τ hτ htτ typical ε hε
  · intro i hi
    rw [sectorEncoder_product]
    exact hf i hi
  · intro i hi
    rw [sectorDecoder_error G i (hσ i) hτ]
    exact hr i hi

section BasisTransport

variable {H S : Type*} [Fintype H] [DecidableEq H] [Fintype S] [DecidableEq S]

/-- Single-Kraus implementation of an isometric basis embedding. -/
def changeBasisChannel (U : Matrix S H ℂ) (hU : Uᴴ * U = 1) : MatrixChannel H S :=
  ofKraus (fun _ : Unit => U) (by simpa using hU)

theorem changeBasisChannel_apply (U : Matrix S H ℂ) (hU : Uᴴ * U = 1)
    (X : Matrix H H ℂ) : (changeBasisChannel U hU).toFun X = U * X * Uᴴ := by
  simp [changeBasisChannel, ofKraus, krausMap]

/-- Pull an input into the Schur basis, then apply its concrete encoder. -/
def transportEncoder (U : Matrix S H ℂ) (hU : U * Uᴴ = 1)
    (E : MatrixChannel H M) : MatrixChannel S M :=
  E.comp (changeBasisChannel Uᴴ (by simpa using hU))

/-- Apply the Schur-basis decoder, then return to the original source basis. -/
def transportDecoder (U : Matrix S H ℂ) (hU : Uᴴ * U = 1)
    (D : MatrixChannel M H) : MatrixChannel M S :=
  (changeBasisChannel U hU).comp D

/-- A unitary change of the source basis preserves the complete roundtrip
error, for the actual transported CPTP channels. -/
theorem transported_roundtrip_error_eq (U : Matrix S H ℂ)
    (hU : Uᴴ * U = 1) (hU' : U * Uᴴ = 1)
    (E : MatrixChannel H M) (D : MatrixChannel M H)
    {ρ : Matrix H H ℂ} (hρ : ρ.PosSemidef) :
    traceDistance ((transportDecoder U hU D).toFun
      ((transportEncoder U hU' E).toFun (U * ρ * Uᴴ))) (U * ρ * Uᴴ) =
      traceDistance (D.toFun (E.toFun ρ)) ρ := by
  have hinverse : (changeBasisChannel Uᴴ (by simpa using hU')).toFun (U * ρ * Uᴴ) = ρ := by
    rw [changeBasisChannel_apply, Matrix.conjTranspose_conjTranspose]
    exact SectorChannels.compress_embed_same U hU ρ
  change traceDistance ((changeBasisChannel U hU).toFun
    (D.toFun (E.toFun ((changeBasisChannel Uᴴ _).toFun (U * ρ * Uᴴ)))))
    (U * ρ * Uᴴ) = _
  rw [hinverse, changeBasisChannel_apply]
  exact traceDistance_isometry U hU (D.positive _ (E.positive _ hρ)) hρ

end BasisTransport

/-- Finite protocol theorem in the original source basis. The given unitary
may be the Schur transform; the source's exact decomposition is shown
explicitly in the conclusion, while both quantum channels are constructed. -/
theorem typical_roundtrip_error_in_basis {S : Type*} [Fintype S] [DecidableEq S]
    (U : Matrix S (Σ i, B i × A i) ℂ) (hU : Uᴴ * U = 1) (hU' : U * Uᴴ = 1)
    (F : ∀ i, MatrixChannel (B i) M) (G : ∀ i, MatrixChannel M (B i))
    (q : ι → ℝ) (hq0 : ∀ i, 0 ≤ q i) (hq1 : ∑ i, q i = 1)
    (σ : ∀ i, Matrix (B i) (B i) ℂ) (hσ : ∀ i, (σ i).PosSemidef)
    (htσ : ∀ i, (σ i).trace = 1) (τ : Matrix M M ℂ)
    (hτ : τ.PosSemidef) (htτ : τ.trace = 1)
    (typical : Finset ι) (ε : ℝ) (hε : 0 ≤ ε)
    (hf : ∀ i ∈ typical, traceDistance ((F i).toFun (σ i)) τ ≤ ε)
    (hr : ∀ i ∈ typical, traceDistance ((G i).toFun τ) (σ i) ≤ ε) :
    traceDistance ((transportDecoder U hU (decoder G q hq0 hq1)).toFun
      ((transportEncoder U hU' (encoder F)).toFun
        (U * sourceState q σ * Uᴴ))) (U * sourceState q σ * Uᴴ) ≤
      2 * ε + 2 * Protocol.outsideMass Finset.univ typical q := by
  rw [transported_roundtrip_error_eq U hU hU' _ _ (sourceState_positive q hq0 σ hσ)]
  exact typical_roundtrip_error F G q hq0 hq1 σ hσ htσ τ hτ htτ typical ε hε hf hr

end FreeEntropy.SchurProtocol
