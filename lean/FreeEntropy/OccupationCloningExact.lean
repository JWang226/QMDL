/-
Copyright (c) 2026 Free Entropy formalization contributors.
See LICENSE and NOTICE in the repository root for license and attribution.
-/

import FreeEntropy.OccupationWerner

/-!
# Exact error of the constructed Werner pure-state channel

Testing the target rank-one projection proves the matching lower bound.
Thus the dimension-ratio loss is the exact trace distance, not just an
upper estimate.
-/
noncomputable section
open scoped BigOperators Matrix Kronecker ComplexOrder MatrixOrder
open Matrix
namespace FreeEntropy.OccupationCloning
open Occupation OccupationSplit CartanChannel TraceDistance
set_option backward.isDefEq.respectTransparency false
variable {d : ℕ}

theorem state_idempotent (n : ℕ) (z : Fin d → ℂ) (hz : ∑ i, Complex.normSq (z i) = 1) :
    state n z * state n z = state n z := by
  have hc : star (coefficients (n := n) z) ⬝ᵥ coefficients z = 1 := by
    simpa only [state, TensorPowers.pure, Matrix.trace, Matrix.diag, dotProduct,
      Pi.star_apply, mul_comm] using state_trace n z hz
  change Matrix.vecMulVec (coefficients z) (star (coefficients z)) *
    Matrix.vecMulVec (coefficients z) (star (coefficients z)) = _
  rw [Matrix.vecMulVec_mul_vecMulVec, hc, one_smul]
  rfl

/-- The target pure projection accepts the forward output with exactly the
dimension ratio probability. -/
theorem forward_target_test (n m : ℕ) (hd : 0 < d) (z : Fin d → ℂ)
    (hz : ∑ i, Complex.normSq (z i) = 1) :
    OrbitMemory.tr (state (n + m) z * (forward d n m hd).toFun (state n z)) =
      dimensionRatio d n m := by
  have hr : reverseMap (split (d := d) (n := n) (m := m)) (state (n + m) z) = state n z := by
    rw [reverseMap_eq_kraus]
    exact reverse_state n m z hz
  have hp := sectorMap_trace_pairing (split (d := d) (n := n) (m := m))
    (Fintype.card (Occupation d n)) (Fintype.card (Occupation d (n + m)))
    (state n z) (state (n + m) z)
  rw [sectorAdjoint, hr, Matrix.mul_smul, Matrix.trace_smul, state_idempotent n z hz,
    state_trace n z hz] at hp
  unfold OrbitMemory.tr
  rw [Matrix.trace_mul_comm, forward_apply, hp]
  simp [dimensionRatio]

/-- The exact trace error of the fully constructed pure-state Werner channel. -/
theorem forward_error_exact (d n m : ℕ) (hd : 0 < d) (z : Fin d → ℂ)
    (hz : ∑ i, Complex.normSq (z i) = 1) :
    traceDistance ((forward d n m hd).toFun (state n z)) (state (n + m) z) =
      1 - dimensionRatio d n m := by
  apply le_antisymm (pure_cloning d n m hd z hz).1
  have ht : ((forward d n m hd).toFun (state n z)).trace = (state (n + m) z).trace := by
    rw [(forward d n m hd).trace_preserving, state_trace n z hz, state_trace (n + m) z hz]
  have h := state_measurement_bound ((forward d n m hd).positive _ (state_positive n z))
    (state_positive (n + m) z) ht (state_positive (n + m) z)
    (OrbitMemory.state_le_one (state_positive (n + m) z) (state_trace (n + m) z hz))
  rw [forward_target_test n m hd z hz, state_idempotent (n + m) z hz] at h
  have ht' : OrbitMemory.tr (state (n + m) z) = 1 := by
    simp [OrbitMemory.tr, state_trace (n + m) z hz]
  rw [ht', abs_of_nonpos (sub_nonpos.mpr (dimensionRatio_le_one d n m hd))] at h
  linarith

end FreeEntropy.OccupationCloning
