/-
Copyright (c) 2026 Free Entropy formalization contributors.
See LICENSE and NOTICE in the repository root for license and attribution.
-/

import FreeEntropy.OrbitMemory
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Algebra.Star.StarProjection
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.Abel

/-!
# From projector perturbation to block operator inequalities

The norm here is the Euclidean operator norm, not the entrywise matrix norm.
This closes the linear-algebra step from the paper's projector perturbation
estimate to its two positive block inequalities. The representation-specific
Casimir estimate itself is not assumed to be a theorem of this module.
-/

noncomputable section
open Matrix
open scoped MatrixOrder ComplexOrder Matrix.Norms.L2Operator

namespace FreeEntropy.ProjectorGeometry
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
set_option linter.unusedSectionVars false
variable {H : Type*} [Fintype H] [DecidableEq H]

/-- Mathlib supplies the Euclidean operator-norm C*-ring and normed-algebra
instances separately. Bundle those existing instances for the C*-order API. -/
local instance matrixL2CStarAlgebra : CStarAlgebra (Matrix H H ℂ) where

theorem scalar_smul_mono {P : Matrix H H ℂ} (hP : P.PosSemidef)
    {a b : ℝ} (hab : a ≤ b) : a • P ≤ b • P := by
  apply Matrix.le_iff.mpr
  rw [← sub_smul]
  exact hP.smul (sub_nonneg.mpr hab)

theorem conjugate_mono {A B : Matrix H H ℂ} (hAB : A ≤ B) (V : Matrix H H ℂ) :
    V * A * Vᴴ ≤ V * B * Vᴴ := by
  apply Matrix.le_iff.mpr
  have h := (Matrix.le_iff.mp hAB).mul_mul_conjTranspose_same V
  simpa only [Matrix.mul_sub, Matrix.sub_mul] using h

theorem projector_square_compression {P Q : Matrix H H ℂ}
    (hP : IsStarProjection P) (hQ : IsStarProjection Q) :
    P * ((P - Q) * (P - Q)) * P = P - P * Q * P := by
  calc
    _ = (P * P) * (P * P) - (P * P) * Q * P -
        P * Q * (P * P) + P * (Q * Q) * P := by noncomm_ring
    _ = P - P * Q * P := by
      rw [hP.isIdempotentElem.eq, hQ.isIdempotentElem.eq, hP.isIdempotentElem.eq]
      abel

/-- Squared operator-norm proximity controls each compressed deficit. -/
theorem projector_deficit_le_of_norm {P Q : Matrix H H ℂ} {e : ℝ}
    (hP : IsStarProjection P) (hQ : IsStarProjection Q)
    (hnorm : ‖P - Q‖ ^ 2 ≤ e) :
    P - P * Q * P ≤ e • P := by
  have hstar : star (P - Q) = P - Q := (hP.isSelfAdjoint.sub hQ.isSelfAdjoint).star_eq
  have hsquare : (P - Q) * (P - Q) ≤ e • (1 : Matrix H H ℂ) := by
    calc
      _ = star (P - Q) * (P - Q) := by rw [hstar]
      _ ≤ algebraMap ℝ (Matrix H H ℂ) (‖P - Q‖ ^ 2) :=
        CStarAlgebra.star_mul_le_algebraMap_norm_sq (a := P - Q)
      _ ≤ e • (1 : Matrix H H ℂ) := by
        rw [Algebra.algebraMap_eq_smul_one]
        exact scalar_smul_mono Matrix.PosSemidef.one hnorm
  have h := conjugate_mono hsquare P
  have hPH : Pᴴ = P := hP.isSelfAdjoint.star_eq
  rw [hPH, projector_square_compression hP hQ] at h
  simpa only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one,
    hP.isIdempotentElem.eq] using h

/-- The forward and reverse block inequalities used in Theorem 2. -/
theorem projector_block_bounds {P Q : Matrix H H ℂ} {e : ℝ}
    (hP : IsStarProjection P) (hQ : IsStarProjection Q)
    (hnorm : ‖P - Q‖ ^ 2 ≤ e) :
    (1 - e) • P ≤ P * Q * P ∧ (1 - e) • Q ≤ Q * P * Q := by
  have hp := projector_deficit_le_of_norm hP hQ hnorm
  have hq := projector_deficit_le_of_norm hQ hP
    (by simpa only [norm_sub_rev] using hnorm)
  constructor
  · rw [sub_smul, one_smul]
    exact sub_le_iff_le_add.mpr (by
      simpa only [add_comm] using sub_le_iff_le_add.mp hp)
  · rw [sub_smul, one_smul]
    exact sub_le_iff_le_add.mpr (by
      simpa only [add_comm] using sub_le_iff_le_add.mp hq)

/-- A Casimir gap and its compressed deficit already imply the reverse
block inequality without any projector-norm or trace-distance hypothesis. -/
theorem compressed_gap_bound {P Q A : Matrix H H ℂ} {gap deficit : ℝ}
    (hQ : IsStarProjection Q) (hgap : 0 < gap)
    (hspectral : gap • (1 - P) ≤ A)
    (hcompression : Q * A * Q = deficit • Q) :
    (1 - deficit / gap) • Q ≤ Q * P * Q := by
  have h := conjugate_mono hspectral Q
  have hQH : Qᴴ = Q := hQ.isSelfAdjoint.star_eq
  rw [hQH, hcompression] at h
  have halg : Q * (gap • (1 - P)) * Q = gap • (Q - Q * P * Q) := by
    rw [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_sub, Matrix.mul_one,
      Matrix.sub_mul, hQ.isIdempotentElem.eq, smul_sub]
  rw [halg] at h
  have hscaled := (Matrix.le_iff.mp h).smul (inv_nonneg.mpr hgap.le)
  have hbound : Q - Q * P * Q ≤ (deficit / gap) • Q := by
    apply Matrix.le_iff.mpr
    simpa only [smul_sub, smul_smul, inv_mul_cancel₀ hgap.ne', one_smul,
      div_eq_mul_inv, mul_comm] using hscaled
  rw [sub_smul, one_smul]
  exact sub_le_iff_le_add.mpr (by
    simpa only [add_comm] using sub_le_iff_le_add.mp hbound)

end FreeEntropy.ProjectorGeometry
