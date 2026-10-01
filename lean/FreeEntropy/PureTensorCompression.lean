/-
Copyright (c) 2026 Free Entropy formalization contributors.
See LICENSE and NOTICE in the repository root for license and attribution.
-/

import FreeEntropy.Occupation
import FreeEntropy.IsometricCompression

/-!
# Exact CPTP compression of every pure tensor-power source

The encoder and decoder are fixed for d and n. Their memory is the actual
occupation basis. Every pure tensor power, including every unitary orbit
of a fixed pure state, is recovered exactly. No representation decomposition,
cloning estimate, or source-identification hypothesis occurs here.
-/
noncomputable section
open scoped BigOperators MatrixOrder ComplexOrder
open Matrix
namespace FreeEntropy.PureTensorCompression
open Occupation TensorPowers TraceDistance
set_option backward.isDefEq.respectTransparency false

/-- The all-zero-letter occupation is a fixed replacement state for failures. -/
def defaultOccupation (d n : ℕ) (hd : 0 < d) : Occupation d n :=
  ofWord (fun _ => ⟨0, hd⟩)

def encoder (d n : ℕ) (hd : 0 < d) :
    Channels.MatrixChannel (Fin n → Fin d) (Occupation d n) :=
  IsometricCompression.encoder basis basis_isometry (defaultOccupation d n hd)

def decoder (d n : ℕ) : Channels.MatrixChannel (Occupation d n) (Fin n → Fin d) :=
  IsometricCompression.decoder basis basis_isometry

/-- A fixed pair of actual completely positive trace-preserving channels
recovers every pure tensor power exactly. -/
theorem roundtrip (d n : ℕ) (hd : 0 < d) (z : Fin d → ℂ) :
    (decoder d n).toFun ((encoder d n hd).toFun (matrix n (pure z))) = matrix n (pure z) := by
  rw [tensor_pure_embedding]
  exact IsometricCompression.roundtrip_embedding basis basis_isometry
    (defaultOccupation d n hd) (pure (coefficients z))

theorem error_zero (d n : ℕ) (hd : 0 < d) (z : Fin d → ℂ) :
    traceDistance ((decoder d n).toFun ((encoder d n hd).toFun (matrix n (pure z))))
      (matrix n (pure z)) = 0 := by
  rw [roundtrip]
  simp [traceDistance, traceNorm, OrbitMemory.tr]

/-- Positivity and normalization of the physical pure tensor-power state. -/
theorem source_state (d n : ℕ) (z : Fin d → ℂ) (hz : ∑ i, Complex.normSq (z i) = 1) :
    (matrix n (pure z)).PosSemidef ∧ (matrix n (pure z)).trace = 1 := by
  apply matrix_state
  · exact Matrix.posSemidef_vecMulVec_self_star z
  · have h := congrArg (fun a : ℝ => (a : ℂ)) hz
    simpa only [TensorPowers.pure, Matrix.trace, Matrix.diag, Complex.star_def, Complex.mul_conj,
      Complex.ofReal_sum, Complex.ofReal_one] using h

/-- Exact compression applies uniformly to an arbitrary family of pure vectors. -/
theorem uniform_error_zero {G : Type*} (d n : ℕ) (hd : 0 < d) (z : G → Fin d → ℂ) :
    ∀ g, traceDistance ((decoder d n).toFun
      ((encoder d n hd).toFun (matrix n (pure (z g))))) (matrix n (pure (z g))) = 0 :=
  fun g => error_zero d n hd (z g)

end FreeEntropy.PureTensorCompression
