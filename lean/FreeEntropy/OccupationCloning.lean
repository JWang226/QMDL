/-
Copyright (c) 2026 Free Entropy formalization contributors.
See LICENSE and NOTICE in the repository root for license and attribution.
-/

import FreeEntropy.OccupationSplitRepresentation
import FreeEntropy.PureTensorCompression
import FreeEntropy.MultiplicityChannels
import FreeEntropy.CartanBalance

/-!
# Concrete symmetric-power reverse cloning

The Cartan inclusion is constructed from word types, not supplied as data.
Its reverse partial-trace channel returns every normalized pure occupation
state exactly. Normalization of the pure occupation states follows from the
actual physical tensor-power matrix and the proved isometry.
-/
noncomputable section
open scoped BigOperators Matrix Kronecker ComplexOrder MatrixOrder
open Matrix
namespace FreeEntropy.OccupationCloning
open Occupation OccupationSplit TensorPowers CartanChannel TraceDistance
set_option backward.isDefEq.respectTransparency false
variable {d n m : ℕ}

/-- The pure state in actual normalized occupation coordinates. -/
def state (n : ℕ) (z : Fin d → ℂ) : Matrix (Occupation d n) (Occupation d n) ℂ :=
  TensorPowers.pure (coefficients z)

theorem state_positive (n : ℕ) (z : Fin d → ℂ) : (state n z).PosSemidef :=
  Matrix.posSemidef_vecMulVec_self_star _

theorem state_trace (n : ℕ) (z : Fin d → ℂ) (hz : ∑ i, Complex.normSq (z i) = 1) :
    (state n z).trace = 1 := by
  have h := congrArg Matrix.trace (tensor_pure_embedding (n := n) z)
  rw [Matrix.trace_mul_cycle, basis_isometry, Matrix.one_mul] at h
  exact h.symm.trans (PureTensorCompression.source_state d n z hz).2

/-- The constructed reverse Cartan channel from n+m to n occupations. -/
def reverse (d n m : ℕ) : Channels.MatrixChannel (Occupation d (n + m)) (Occupation d n) :=
  reverseChannel split split_isometry

/-- Reverse pure cloning is exact, for the literal finite CPTP channel. -/
theorem reverse_state (n m : ℕ) (z : Fin d → ℂ) (hz : ∑ i, Complex.normSq (z i) = 1) :
    (reverse d n m).toFun (state (n + m) z) = state n z := by
  rw [reverse, reverseChannel_apply]
  change partialTrace (split * TensorPowers.pure (coefficients (n := n + m) z) * splitᴴ) = _
  rw [split_pure, MultiplicityChannels.partialTrace_kronecker]
  rw [show (TensorPowers.pure (coefficients (n := m) z)).trace = 1 from state_trace m z hz,
    one_smul]
  rfl

theorem reverse_error_zero (n m : ℕ) (z : Fin d → ℂ) (hz : ∑ i, Complex.normSq (z i) = 1) :
    traceDistance ((reverse d n m).toFun (state (n + m) z)) (state n z) = 0 := by
  rw [reverse_state n m z hz]
  simp [traceDistance, traceNorm, OrbitMemory.tr]

end FreeEntropy.OccupationCloning
