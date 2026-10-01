/-
Copyright (c) 2026 Free Entropy formalization contributors.
See LICENSE and NOTICE in the repository root for license and attribution.
-/

import FreeEntropy.AtypicalChannels

/-!
# Exact compression of an isometrically embedded subspace

Both directions are actual CPTP maps. The encoder uses the inverse isometry
on its range and a pure-state replacement on the orthogonal complement.
It recovers every matrix supported in the embedded memory space exactly.
-/
noncomputable section
open scoped BigOperators MatrixOrder ComplexOrder
open Matrix
namespace FreeEntropy.IsometricCompression
open Channels AtypicalChannels SchurProtocol
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
variable {H M : Type*} [Fintype H] [Fintype M] [DecidableEq H] [DecidableEq M]

def complement (V : Matrix H M ℂ) : Matrix H H ℂ := 1 - V * Vᴴ

theorem complement_adjoint (V : Matrix H M ℂ) : (complement V)ᴴ = complement V := by
  simp [complement]

theorem complement_mul (V : Matrix H M ℂ) (hV : Vᴴ * V = 1) : complement V * V = 0 := by
  simp only [complement, Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc, hV, Matrix.mul_one,
    sub_self]

theorem complement_idempotent (V : Matrix H M ℂ) (hV : Vᴴ * V = 1) :
    complement V * complement V = complement V := by
  have h := complement_mul V hV
  unfold complement at h ⊢
  rw [Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc, h, Matrix.zero_mul, sub_zero]

def encoderKraus (V : Matrix H M ℂ) (target : M) : Unit ⊕ H → Matrix M H ℂ :=
  Sum.elim (fun _ => Vᴴ) (fun a => replacementKraus target a * complement V)

theorem encoderKraus_normalization (V : Matrix H M ℂ) (hV : Vᴴ * V = 1) (target : M) :
    (∑ a, (encoderKraus V target a)ᴴ * encoderKraus V target a) = 1 := by
  rw [Fintype.sum_sum_type]
  simp only [encoderKraus, Sum.elim_inl, Sum.elim_inr, Fintype.sum_unique,
    Matrix.conjTranspose_conjTranspose, Matrix.conjTranspose_mul, complement_adjoint]
  have hs : (∑ a : H, complement V * (replacementKraus target a)ᴴ *
      (replacementKraus target a * complement V)) = complement V := by
    calc
      _ = complement V * (∑ a : H, (replacementKraus target a)ᴴ *
          replacementKraus target a) * complement V := by
        simp only [Matrix.mul_sum, Matrix.sum_mul, Matrix.mul_assoc]
      _ = complement V := by
        rw [replacementKraus_normalization, Matrix.mul_one, complement_idempotent V hV]
  rw [hs]
  simp [complement]

def encoder (V : Matrix H M ℂ) (hV : Vᴴ * V = 1) (target : M) : MatrixChannel H M :=
  ofKraus (encoderKraus V target) (encoderKraus_normalization V hV target)

def decoder (V : Matrix H M ℂ) (hV : Vᴴ * V = 1) : MatrixChannel M H :=
  changeBasisChannel V hV

theorem decoder_apply (V : Matrix H M ℂ) (hV : Vᴴ * V = 1) (Y : Matrix M M ℂ) :
    (decoder V hV).toFun Y = V * Y * Vᴴ := changeBasisChannel_apply V hV Y

theorem encoder_apply (V : Matrix H M ℂ) (hV : Vᴴ * V = 1) (target : M)
    (X : Matrix H H ℂ) :
    (encoder V hV target).toFun X = Vᴴ * X * V +
      (replacementChannel target).toFun (complement V * X * complement V) := by
  simp only [encoder, replacementChannel, ofKraus, krausMap, Fintype.sum_sum_type,
    encoderKraus, Sum.elim_inl, Sum.elim_inr, Fintype.sum_unique,
    Matrix.conjTranspose_conjTranspose, Matrix.conjTranspose_mul, complement_adjoint]
  congr 1
  apply Finset.sum_congr rfl
  intro a _
  simp only [Matrix.mul_assoc]

/-- Exact encoding on the embedded memory subspace. -/
theorem encoder_embedding (V : Matrix H M ℂ) (hV : Vᴴ * V = 1) (target : M)
    (Y : Matrix M M ℂ) :
    (encoder V hV target).toFun (V * Y * Vᴴ) = Y := by
  rw [encoder_apply]
  have hmain : Vᴴ * (V * Y * Vᴴ) * V = Y := by
    calc
      _ = (Vᴴ * V) * Y * (Vᴴ * V) := by simp only [Matrix.mul_assoc]
      _ = Y := by rw [hV, Matrix.one_mul, Matrix.mul_one]
  have hzero : complement V * (V * Y * Vᴴ) * complement V = 0 := by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, complement_mul V hV]
    simp
  rw [hmain, hzero, replacementChannel_apply]
  simp

/-- A single fixed encoder/decoder pair reconstructs every embedded state exactly. -/
theorem roundtrip_embedding (V : Matrix H M ℂ) (hV : Vᴴ * V = 1) (target : M)
    (Y : Matrix M M ℂ) :
    (decoder V hV).toFun ((encoder V hV target).toFun (V * Y * Vᴴ)) = V * Y * Vᴴ := by
  rw [encoder_embedding, decoder_apply]

end FreeEntropy.IsometricCompression
