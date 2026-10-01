/-
Copyright (c) 2026 Free Entropy formalization contributors.
See LICENSE and NOTICE in the repository root for license and attribution.
-/

import FreeEntropy.PureAchievability
import FreeEntropy.OccupationIrreducible
import FreeEntropy.QuantumTransfer

/-! The physical pure-tensor converse, through the actual occupation isometry. -/

noncomputable section
open Matrix MeasureTheory Filter
open scoped BigOperators Topology ComplexOrder MatrixOrder Matrix.Norms.Elementwise

namespace FreeEntropy.PureTensorCompression
open Occupation TensorPowers TraceDistance Channels Twirling
set_option backward.isDefEq.respectTransparency false

variable {d n : ℕ}

def occupationState (n : ℕ) (z : Fin d → ℂ) :
    Matrix (Occupation d n) (Occupation d n) ℂ := pure (coefficients z)

theorem occupationState_positive (n : ℕ) (z : Fin d → ℂ) :
    (occupationState n z).PosSemidef := Matrix.posSemidef_vecMulVec_self_star _

theorem occupationState_trace (n : ℕ) (z : Fin d → ℂ)
    (hz : ∑ i, Complex.normSq (z i) = 1) : (occupationState n z).trace = 1 := by
  have ht := (source_state d n z hz).2
  rw [tensor_pure_embedding, Matrix.trace_mul_cycle, basis_isometry, Matrix.one_mul] at ht
  exact ht

theorem pure_idempotent_of_trace {H : Type*} [Fintype H] (v : H → ℂ)
    (hv : (pure v).trace = 1) : pure v * pure v = pure v := by
  change vecMulVec v (star v) * vecMulVec v (star v) = vecMulVec v (star v)
  rw [Matrix.vecMulVec_mul_vecMulVec]
  have hs : star v ⬝ᵥ v = 1 := by
    rw [dotProduct_comm]
    exact hv
  rw [hs, one_smul]

/-- The source is the actual tensor power of the physical unitary orbit. -/
def physicalOrbitState (n : ℕ) (z : Fin d → ℂ) (U : Matrix.unitaryGroup (Fin d) ℂ) :
    Matrix (Fin n → Fin d) (Fin n → Fin d) ℂ :=
  matrix n (U.val * pure z * U.valᴴ)

def occupationOrbitState (n : ℕ) (z : Fin d → ℂ) (U : Matrix.unitaryGroup (Fin d) ℂ) :
    Matrix (Occupation d n) (Occupation d n) ℂ :=
  symmetricMatrix U.val * occupationState n z * (symmetricMatrix U.val)ᴴ

theorem physicalOrbitState_embedding (n : ℕ) (z : Fin d → ℂ)
    (U : Matrix.unitaryGroup (Fin d) ℂ) :
    physicalOrbitState n z U = basis * occupationOrbitState n z U * basisᴴ := by
  unfold physicalOrbitState occupationOrbitState occupationState
  rw [matrix_covariance, tensor_pure_embedding]
  calc
    _ = (matrix n U.val * basis (d := d) (n := n)) * pure (coefficients (n := n) z) *
        (matrix n U.val * basis (d := d) (n := n))ᴴ := by
      simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    _ = _ := by
      rw [symmetricMatrix_intertwines]
      simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]

theorem occupationOrbitState_positive (n : ℕ) (z : Fin d → ℂ)
    (U : Matrix.unitaryGroup (Fin d) ℂ) : (occupationOrbitState n z U).PosSemidef :=
  (occupationState_positive n z).mul_mul_conjTranspose_same _

theorem physicalOrbitState_positive (n : ℕ) (z : Fin d → ℂ)
    (U : Matrix.unitaryGroup (Fin d) ℂ) : (physicalOrbitState n z U).PosSemidef := by
  rw [physicalOrbitState_embedding]
  exact (occupationOrbitState_positive n z U).mul_mul_conjTranspose_same _

theorem occupationOrbitState_continuous (n : ℕ) (z : Fin d → ℂ) :
    Continuous (occupationOrbitState n z) := by
  have h : Continuous (fun U : Matrix.unitaryGroup (Fin d) ℂ =>
      symmetricMatrix (n := n) U.val) :=
    (symmetricMatrix_continuous (d := d) (n := n)).comp continuous_subtype_val
  exact (h.matrix_mul continuous_const).matrix_mul h.matrix_conjTranspose

theorem physicalOrbitState_continuous (n : ℕ) (z : Fin d → ℂ) :
    Continuous (physicalOrbitState n z) := by
  have h : Continuous (fun U : Matrix.unitaryGroup (Fin d) ℂ =>
      basis * occupationOrbitState n z U * basisᴴ) :=
    (continuous_const.matrix_mul (occupationOrbitState_continuous n z)).matrix_mul continuous_const
  simpa only [← physicalOrbitState_embedding] using h

variable {M : Type*} [Fintype M] [DecidableEq M]

/-- Actual Haar-average reconstruction error on physical pure tensor powers. -/
def physicalAverageError (n : ℕ) (z : Fin d → ℂ)
    (E : MatrixChannel (Fin n → Fin d) M) (D : MatrixChannel M (Fin n → Fin d)) : ℝ :=
  ∫ U, traceDistance (D.toFun (E.toFun (physicalOrbitState n z U)))
    (physicalOrbitState n z U) ∂UnitaryHaar.probabilityHaar (Fin d)

/-- Exact compression of the symmetric subspace transfers any physical
code to the genuine irreducible orbit without increasing its average error. -/
theorem transferred_average_error_le (n : ℕ) (hd : 0 < d) (z : Fin d → ℂ)
    (E : MatrixChannel (Fin n → Fin d) M) (D : MatrixChannel M (Fin n → Fin d)) :
    (∫ U, traceDistance (((encoder d n hd).comp D).toFun
      ((E.comp (decoder d n)).toFun (occupationOrbitState n z U)))
      (occupationOrbitState n z U) ∂UnitaryHaar.probabilityHaar (Fin d)) ≤
      physicalAverageError n z E D := by
  have h := QuantumTransfer.compact_transferred_average_error_le
    (UnitaryHaar.probabilityHaar (Fin d)) (encoder d n hd) (decoder d n) E D
    (physicalOrbitState n z) (occupationOrbitState n z)
    (physicalOrbitState_continuous n z) (occupationOrbitState_continuous n z)
    (physicalOrbitState_positive n z) (occupationOrbitState_positive n z)
    (physicalAverageError n z E D) 0 0 le_rfl ?_ ?_
  · simpa only [add_zero] using h
  · intro U
    rw [physicalOrbitState_embedding]
    change traceDistance ((IsometricCompression.encoder basis basis_isometry
      (defaultOccupation d n hd)).toFun (basis * occupationOrbitState n z U * basisᴴ))
        (occupationOrbitState n z U) ≤ 0
    rw [IsometricCompression.encoder_embedding]
    simp [traceDistance, traceNorm, OrbitMemory.tr]
  · intro U
    rw [physicalOrbitState_embedding]
    change traceDistance ((IsometricCompression.decoder basis basis_isometry).toFun
      (occupationOrbitState n z U)) (basis * occupationOrbitState n z U * basisᴴ) ≤ 0
    rw [IsometricCompression.decoder_apply]
    simp [traceDistance, traceNorm, OrbitMemory.tr]

/-- The exact finite memory converse for the actual physical pure-state
orbit of U(d), with no supplied representation, twirling, or spectral data. -/
theorem pure_memory_bound (n : ℕ) (hd : 0 < d) (z : Fin d → ℂ)
    (hz : ∑ i, Complex.normSq (z i) = 1)
    (E : MatrixChannel (Fin n → Fin d) M) (D : MatrixChannel M (Fin n → Fin d)) :
    (Fintype.card (Occupation d n) : ℝ) * (1 - physicalAverageError n z E D) ≤
      (Fintype.card M : ℝ) := by
  letI : Nonempty (Occupation d n) := ⟨defaultOccupation d n hd⟩
  letI := unitaryRepresentation_irreducible d n hd
  let E' := E.comp (decoder d n)
  let D' := (encoder d n hd).comp D
  have ht := occupationState_trace n z hz
  have hP := occupationState_positive n z
  have hp : OrbitMemory.tr (occupationState n z * occupationState n z) = 1 := by
    have hsq : occupationState n z * occupationState n z = occupationState n z :=
      pure_idempotent_of_trace _ ht
    rw [hsq, OrbitMemory.tr, ht]
    rfl
  have hs : occupationState n z ≤ (0 : ℝ) • (1 : Matrix (Occupation d n) (Occupation d n) ℂ) +
      ((1 : ℝ) - 0) • occupationState n z := by simp
  have h := OrbitTraceDistance.irreducible_orbit_memory_bound
    (UnitaryHaar.probabilityHaar (Fin d)) (unitaryRepresentation d n)
    (unitaryRepresentation_continuous d n) (unitaryRepresentation_unitary d n)
    E'.toRealLinearMap D'.toRealLinearMap E'.positive D'.positive
    E'.trace_preserving D'.trace_preserving (occupationState n z) (occupationState n z)
    hP ht hP (by norm_num : (0 : ℝ) < 1 - 0) hp hs
  have herr := transferred_average_error_le n hd z E D
  have hbound : (Fintype.card (Occupation d n) : ℝ) *
      (1 - (∫ U, traceDistance (D'.toFun (E'.toFun (occupationOrbitState n z U)))
        (occupationOrbitState n z U) ∂UnitaryHaar.probabilityHaar (Fin d))) ≤
      (Fintype.card M : ℝ) := by
    simpa only [sub_zero, div_one] using h
  exact (mul_le_mul_of_nonneg_left (sub_le_sub_left herr 1) (Nat.cast_nonneg _)).trans hbound

/-- The exact qmdl liminf converse for arbitrary channels on the actual
pure tensor-power source, with vanishing actual Haar-average error. -/
theorem theorem1_pure_converse {d : ℕ} (s : FixedSpectrum d 1)
    (z : Fin d → ℂ) (hz : ∑ i, Complex.normSq (z i) = 1)
    (memory : ℕ → ℕ)
    (E : ∀ n, MatrixChannel (Fin n → Fin d) (Fin (memory n)))
    (D : ∀ n, MatrixChannel (Fin (memory n)) (Fin n → Fin d))
    (herror : Tendsto (fun n => physicalAverageError n z (E n) (D n)) atTop (𝓝 0)) :
    (0 : EReal) ≤ liminf
      (fun n => ((Real.logb 2 (memory n) - Weyl.qmdl d 1 s.eigenvalue n : ℝ) : EReal))
      atTop := by
  have hd : 0 < d := lt_of_lt_of_le s.rank_pos s.rank_le
  apply optimal_memory_converse (γ := 1)
    (targetDim := fun n => Fintype.card (Occupation d n))
    (error := fun n => physicalAverageError n z (E n) (D n))
    (transferError := fun _ => 0) (by norm_num)
    (fun n => occupationDimension_pos d n hd) herror tendsto_const_nhds
    (occupation_qmdl_asymptotic s)
  apply Eventually.of_forall
  intro n
  simpa only [add_zero, div_one, Fintype.card_fin] using pure_memory_bound n hd z hz (E n) (D n)

end FreeEntropy.PureTensorCompression
