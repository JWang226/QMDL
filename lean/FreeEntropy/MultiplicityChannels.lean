/-
Copyright (c) 2026 Free Entropy formalization contributors.
See LICENSE and NOTICE in the repository root for license and attribution.
-/

import FreeEntropy.CartanChannel
import FreeEntropy.TraceDistance

/-!
# Discarding and restoring a maximally mixed multiplicity register

Both operations are concrete CPTP maps. Appending the normalized identity
is the explicit Cartan/Kraus map at the identity inclusion, and discarding
is the actual matrix partial trace. Their left-inverse identity also proves
exact trace-distance preservation on states with the restored register.
-/

noncomputable section
open scoped BigOperators Matrix Kronecker ComplexOrder MatrixOrder
open Matrix

namespace FreeEntropy.MultiplicityChannels
open Channels CartanChannel TraceDistance

set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false

variable {B A : Type*} [Fintype B] [Fintype A] [DecidableEq B] [DecidableEq A]

def maximallyMixed (A : Type*) [Fintype A] [DecidableEq A] : Matrix A A ℂ :=
  (Fintype.card A : ℝ)⁻¹ • (1 : Matrix A A ℂ)

theorem maximallyMixed_positive : (maximallyMixed A).PosSemidef :=
  Matrix.PosSemidef.one.smul (inv_nonneg.mpr (Nat.cast_nonneg _ : (0 : ℝ) ≤ Fintype.card A))

theorem maximallyMixed_trace [Nonempty A] : (maximallyMixed A).trace = 1 := by
  simp [maximallyMixed, Matrix.trace_smul, Matrix.trace_one, Complex.real_smul,
    Fintype.card_ne_zero]

/-- The literal tensor product with the normalized identity on the
multiplicity space. -/
def appendMap (X : Matrix B B ℂ) : Matrix (B × A) (B × A) ℂ :=
  X ⊗ₖ maximallyMixed A

theorem partialTrace_kronecker (X : Matrix B B ℂ) (Y : Matrix A A ℂ) :
    partialTrace (X ⊗ₖ Y) = Y.trace • X := by
  ext i j
  simp only [partialTrace, Matrix.kronecker_apply, Matrix.trace, Matrix.diag,
    Matrix.smul_apply, smul_eq_mul]
  rw [← Finset.mul_sum, mul_comm]

theorem identity_balance :
    partialTrace (1 : Matrix (B × A) (B × A) ℂ) =
      (Fintype.card A : ℝ) • (1 : Matrix B B ℂ) := by
  ext i j
  by_cases hij : i = j <;>
    simp [partialTrace, Matrix.one_apply, Matrix.smul_apply, hij, Complex.real_smul]

/-- Appending the normalized identity, with its actual Kraus proof of CPTP. -/
def appendChannel [Nonempty A] : MatrixChannel B (B × A) :=
  cartanChannel (1 : Matrix (B × A) (B × A) ℂ) 1 (Fintype.card A)
    zero_lt_one (by exact_mod_cast Fintype.card_pos) (by
      simpa using (identity_balance (B := B) (A := A)))

theorem appendChannel_apply [Nonempty A] (X : Matrix B B ℂ) :
    (appendChannel (B := B) (A := A)).toFun X = appendMap (A := A) X := by
  rw [appendChannel, cartanChannel_apply]
  simp only [sectorMap, Matrix.conjTranspose_one, Matrix.one_mul, Matrix.mul_one,
    one_div, appendMap, maximallyMixed, Matrix.kronecker_smul]

/-- Discard the multiplicity register by the literal partial trace. -/
def discardChannel : MatrixChannel (B × A) B := partialTraceChannel

theorem discardChannel_apply (X : Matrix (B × A) (B × A) ℂ) :
    (discardChannel (B := B) (A := A)).toFun X = partialTrace X :=
  partialTraceChannel_apply X

theorem discard_product (X : Matrix B B ℂ) (Y : Matrix A A ℂ) (hY : Y.trace = 1) :
    (discardChannel (B := B) (A := A)).toFun (X ⊗ₖ Y) = X := by
  rw [discardChannel_apply, partialTrace_kronecker, hY, one_smul]

/-- Restoring then discarding the ancillary state is exactly the identity. -/
theorem discard_append [Nonempty A] (X : Matrix B B ℂ) :
    (discardChannel (B := B) (A := A)).toFun
      ((appendChannel (B := B) (A := A)).toFun X) = X := by
  rw [appendChannel_apply]
  exact discard_product X (maximallyMixed A) maximallyMixed_trace

/-- Product states with the maximally mixed register are recovered exactly
after that register is discarded and restored. -/
theorem append_discard_product [Nonempty A] (X : Matrix B B ℂ) :
    (appendChannel (B := B) (A := A)).toFun
      ((discardChannel (B := B) (A := A)).toFun (X ⊗ₖ maximallyMixed A)) =
      X ⊗ₖ maximallyMixed A := by
  rw [discard_product X (maximallyMixed A) maximallyMixed_trace, appendChannel_apply]
  rfl

theorem appendMap_positive [Nonempty A] {X : Matrix B B ℂ} (hX : X.PosSemidef) :
    (appendMap (A := A) X).PosSemidef := by
  rw [← appendChannel_apply]
  exact appendChannel.positive X hX

theorem appendMap_trace [Nonempty A] (X : Matrix B B ℂ) :
    (appendMap (A := A) X).trace = X.trace := by
  rw [← appendChannel_apply]
  exact appendChannel.trace_preserving X

/-- CPTP contraction in both directions proves exact preservation of trace
distance when the same maximally mixed multiplicity register is appended. -/
theorem traceDistance_append [Nonempty A] {X Y : Matrix B B ℂ}
    (hX : X.PosSemidef) (hY : Y.PosSemidef) :
    traceDistance (appendMap (A := A) X) (appendMap (A := A) Y) = traceDistance X Y := by
  let E := appendChannel (B := B) (A := A)
  let D := discardChannel (B := B) (A := A)
  apply le_antisymm
  · have h := traceDistance_contract E.toRealLinearMap E.positive E.trace_preserving hX hY
    change traceDistance (E.toFun X) (E.toFun Y) ≤ traceDistance X Y at h
    simpa only [E, appendChannel_apply] using h
  · have h := traceDistance_contract D.toRealLinearMap D.positive D.trace_preserving
      (E.positive X hX) (E.positive Y hY)
    change traceDistance (D.toFun (E.toFun X)) (D.toFun (E.toFun Y)) ≤
      traceDistance (E.toFun X) (E.toFun Y) at h
    dsimp only [D, E] at h
    rw [discard_append, discard_append] at h
    simpa only [appendChannel_apply] using h

end FreeEntropy.MultiplicityChannels
