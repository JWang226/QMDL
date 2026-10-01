/-
Copyright (c) 2026 Free Entropy formalization contributors.
See LICENSE and NOTICE in the repository root for license and attribution.
-/

import FreeEntropy.OccupationCloningExact
import FreeEntropy.OccupationRatio

/-!
# Theorem 2 for all pure tensor-power states

This is an unconditional rank-one instance in every positive physical
dimension. Both the intrinsic symmetric-power channels and channels on the
literal tensor-power matrices are constructed. Their exact errors imply the
manuscript's finite rate with C=d−1, D=m, and the row gap b=n.
-/
noncomputable section
open scoped BigOperators Matrix Kronecker ComplexOrder MatrixOrder
open Matrix
namespace FreeEntropy.OccupationCloning
open Occupation OccupationSplit CartanChannel TraceDistance TensorPowers
set_option backward.isDefEq.respectTransparency false

/-- The manuscript's cloning-accuracy rate for genuine rank-one irreps,
with all representation and channel data constructed. -/
theorem theorem2_pure_cloning (d n m : ℕ) (hd : 0 < d) (z : Fin d → ℂ)
    (hz : ∑ i, Complex.normSq (z i) = 1) :
    traceDistance ((forward d n m hd).toFun (state n z)) (state (n + m) z) ≤
        ((d - 1 : ℕ) : ℝ) * m / ((n : ℝ) + 1) ∧
      traceDistance ((reverse d n m).toFun (state (n + m) z)) (state n z) ≤
        ((d - 1 : ℕ) : ℝ) * m / ((n : ℝ) + 1) := by
  constructor
  · rw [forward_error_exact d n m hd z hz]
    exact dimensionRatio_loss_le d n m hd
  · rw [reverse_error_zero n m z hz]
    positivity

/-- Forward cloning as a channel on the literal tensor-word Hilbert spaces. -/
def physicalForward (d n m : ℕ) (hd : 0 < d) :
    Channels.MatrixChannel (Fin n → Fin d) (Fin (n + m) → Fin d) :=
  (PureTensorCompression.decoder d (n + m)).comp
    ((forward d n m hd).comp (PureTensorCompression.encoder d n hd))

/-- Reverse cloning on the literal tensor-word Hilbert spaces. -/
def physicalReverse (d n m : ℕ) (hd : 0 < d) :
    Channels.MatrixChannel (Fin (n + m) → Fin d) (Fin n → Fin d) :=
  (PureTensorCompression.decoder d n).comp
    ((reverse d n m).comp (PureTensorCompression.encoder d (n + m) hd))

theorem physicalForward_apply (d n m : ℕ) (hd : 0 < d) (z : Fin d → ℂ) :
    (physicalForward d n m hd).toFun (matrix n (TensorPowers.pure z)) =
      basis * (forward d n m hd).toFun (state n z) * basisᴴ := by
  change (IsometricCompression.decoder basis basis_isometry).toFun
    ((forward d n m hd).toFun ((IsometricCompression.encoder basis basis_isometry
      (PureTensorCompression.defaultOccupation d n hd)).toFun (matrix n (TensorPowers.pure z)))) = _
  rw [tensor_pure_embedding, IsometricCompression.encoder_embedding, IsometricCompression.decoder_apply]
  rfl

theorem physicalReverse_exact (d n m : ℕ) (hd : 0 < d) (z : Fin d → ℂ)
    (hz : ∑ i, Complex.normSq (z i) = 1) :
    (physicalReverse d n m hd).toFun (matrix (n + m) (TensorPowers.pure z)) =
      matrix n (TensorPowers.pure z) := by
  change (IsometricCompression.decoder basis basis_isometry).toFun
    ((reverse d n m).toFun ((IsometricCompression.encoder basis basis_isometry
      (PureTensorCompression.defaultOccupation d (n + m) hd)).toFun
      (matrix (n + m) (TensorPowers.pure z)))) = _
  rw [tensor_pure_embedding, IsometricCompression.encoder_embedding]
  change (IsometricCompression.decoder basis basis_isometry).toFun
    ((reverse d n m).toFun (state (n + m) z)) = _
  rw [reverse_state n m z hz, IsometricCompression.decoder_apply, tensor_pure_embedding]
  rfl

/-- Exact forward trace distance on the original physical tensor-power source. -/
theorem physicalForward_error_exact (d n m : ℕ) (hd : 0 < d) (z : Fin d → ℂ)
    (hz : ∑ i, Complex.normSq (z i) = 1) :
    traceDistance ((physicalForward d n m hd).toFun (matrix n (TensorPowers.pure z)))
      (matrix (n + m) (TensorPowers.pure z)) = 1 - dimensionRatio d n m := by
  rw [physicalForward_apply, tensor_pure_embedding]
  change traceDistance (basis * (forward d n m hd).toFun (state n z) * basisᴴ)
    (basis * state (n + m) z * basisᴴ) = _
  rw [traceDistance_isometry basis basis_isometry
    ((forward d n m hd).positive _ (state_positive n z)) (state_positive (n + m) z)]
  exact forward_error_exact d n m hd z hz

/-- Theorem 2's rank-one rate for literal tensor-power density matrices. -/
theorem theorem2_physical_pure_cloning (d n m : ℕ) (hd : 0 < d) (z : Fin d → ℂ)
    (hz : ∑ i, Complex.normSq (z i) = 1) :
    traceDistance ((physicalForward d n m hd).toFun (matrix n (TensorPowers.pure z)))
        (matrix (n + m) (TensorPowers.pure z)) ≤ ((d - 1 : ℕ) : ℝ) * m / ((n : ℝ) + 1) ∧
      (physicalReverse d n m hd).toFun (matrix (n + m) (TensorPowers.pure z)) =
        matrix n (TensorPowers.pure z) := by
  exact ⟨(physicalForward_error_exact d n m hd z hz).le.trans (dimensionRatio_loss_le d n m hd),
    physicalReverse_exact d n m hd z hz⟩

end FreeEntropy.OccupationCloning
