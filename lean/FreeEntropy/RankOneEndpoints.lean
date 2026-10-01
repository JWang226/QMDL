/-
Copyright (c) 2026 Free Entropy formalization contributors.
See LICENSE and NOTICE in the repository root for license and attribution.
-/

import FreeEntropy.PureConverse
import FreeEntropy.RankOneStates
import FreeEntropy.OccupationTheorem2

/-!
# Theorems 1 endpoints for actual rank-one density matrices

The input is a positive trace-one matrix with actual matrix rank one.
Its vector presentation is derived from the spectral theorem. Explicit
CPTP compression has zero error uniformly on its physical unitary orbit;
any reliable physical code satisfies the exact qmdl liminf lower bound.
-/

noncomputable section
open Matrix MeasureTheory Filter
open scoped BigOperators Topology ComplexOrder MatrixOrder Matrix.Norms.Elementwise

namespace FreeEntropy.RankOneCompression
open TensorPowers TraceDistance Channels PureTensorCompression Occupation
set_option backward.isDefEq.respectTransparency false

variable {d : ℕ} {M : Type*} [Fintype M] [DecidableEq M]

def orbitState (n : ℕ) (ρ : Matrix (Fin d) (Fin d) ℂ)
    (U : Matrix.unitaryGroup (Fin d) ℂ) : Matrix (Fin n → Fin d) (Fin n → Fin d) ℂ :=
  matrix n (U.val * ρ * U.valᴴ)

def averageError (n : ℕ) (ρ : Matrix (Fin d) (Fin d) ℂ)
    (E : MatrixChannel (Fin n → Fin d) M) (D : MatrixChannel M (Fin n → Fin d)) : ℝ :=
  ∫ U, traceDistance (D.toFun (E.toFun (orbitState n ρ U))) (orbitState n ρ U)
    ∂UnitaryHaar.probabilityHaar (Fin d)

theorem averageError_le_of_uniform (n : ℕ) (ρ : Matrix (Fin d) (Fin d) ℂ)
    (E : MatrixChannel (Fin n → Fin d) M) (D : MatrixChannel M (Fin n → Fin d))
    (δ : ℝ) (hδ : ∀ U, traceDistance (D.toFun (E.toFun (orbitState n ρ U)))
      (orbitState n ρ U) ≤ δ) : averageError n ρ E D ≤ δ := by
  have hc : Continuous (orbitState n ρ) :=
    Occupation.tensor_matrix_continuous.comp
      ((continuous_subtype_val.matrix_mul continuous_const).matrix_mul
        continuous_subtype_val.matrix_conjTranspose)
  have hi := QuantumTransfer.integrable_traceDistance
    (UnitaryHaar.probabilityHaar (Fin d))
    ((QuantumTransfer.channel_continuous D).comp ((QuantumTransfer.channel_continuous E).comp hc)) hc
  have h := integral_mono hi (integrable_const δ) hδ
  simpa only [averageError, integral_const, MeasureTheory.probReal_univ, one_smul] using h

theorem pure_covariance {H K : Type*} [Fintype H] [Fintype K]
    (U : Matrix K H ℂ) (z : H → ℂ) : U * pure z * Uᴴ = pure (U *ᵥ z) := by
  change U * vecMulVec z (star z) * Uᴴ = vecMulVec (U *ᵥ z) (star (U *ᵥ z))
  rw [Matrix.mul_vecMulVec, Matrix.vecMulVec_mul, Matrix.star_mulVec]

/-- Exact physical reconstruction holds on the entire orbit of any
rank-one density matrix, using the same fixed encoder and decoder. -/
theorem rank_one_roundtrip (n : ℕ) (hd : 0 < d) (ρ : Matrix (Fin d) (Fin d) ℂ)
    (hρ : ρ.PosSemidef) (ht : ρ.trace = 1) (hrank : ρ.rank = 1)
    (U : Matrix.unitaryGroup (Fin d) ℂ) :
    (decoder d n).toFun ((encoder d n hd).toFun (orbitState n ρ U)) = orbitState n ρ U := by
  obtain ⟨z, _, rfl⟩ := RankOneStates.exists_normalized_vector ρ hρ ht hrank
  simp only [orbitState, pure_covariance]
  exact roundtrip d n hd (U.val *ᵥ z)

/-- Complete rank-one achievability for the density-matrix input used in
the manuscript: the exact qmdl memory cost and uniformly zero physical error. -/
theorem theorem1_rank_one_achievability (s : FixedSpectrum d 1)
    (ρ : Matrix (Fin d) (Fin d) ℂ) (hρ : ρ.PosSemidef) (ht : ρ.trace = 1)
    (hrank : ρ.rank = 1) :
    Tendsto (fun n : ℕ => Real.logb 2 (Fintype.card (Occupation d n)) -
      Weyl.qmdl d 1 s.eigenvalue n) atTop (𝓝 0) ∧
    ∀ n U, traceDistance ((decoder d n).toFun
      ((encoder d n (lt_of_lt_of_le s.rank_pos s.rank_le)).toFun (orbitState n ρ U)))
        (orbitState n ρ U) = 0 := by
  refine ⟨occupation_qmdl_asymptotic s, ?_⟩
  intro n U
  rw [rank_one_roundtrip n _ ρ hρ ht hrank U]
  simp [traceDistance, traceNorm, OrbitMemory.tr]

/-- Finite physical memory lower bound for an arbitrary rank-one density
matrix, with every spectral and representation fact derived. -/
theorem rank_one_memory_bound (n : ℕ) (hd : 0 < d)
    (ρ : Matrix (Fin d) (Fin d) ℂ) (hρ : ρ.PosSemidef) (ht : ρ.trace = 1)
    (hrank : ρ.rank = 1)
    (E : MatrixChannel (Fin n → Fin d) M) (D : MatrixChannel M (Fin n → Fin d)) :
    (Fintype.card (Occupation d n) : ℝ) * (1 - averageError n ρ E D) ≤
      (Fintype.card M : ℝ) := by
  obtain ⟨z, hz, rfl⟩ := RankOneStates.exists_normalized_vector ρ hρ ht hrank
  exact pure_memory_bound n hd z hz E D

/-- Rank-one qmdl converse using actual Haar-average reconstruction error. -/
theorem theorem1_rank_one_converse (s : FixedSpectrum d 1)
    (ρ : Matrix (Fin d) (Fin d) ℂ) (hρ : ρ.PosSemidef) (ht : ρ.trace = 1)
    (hrank : ρ.rank = 1) (memory : ℕ → ℕ)
    (E : ∀ n, MatrixChannel (Fin n → Fin d) (Fin (memory n)))
    (D : ∀ n, MatrixChannel (Fin (memory n)) (Fin n → Fin d))
    (herror : Tendsto (fun n => averageError n ρ (E n) (D n)) atTop (𝓝 0)) :
    (0 : EReal) ≤ liminf
      (fun n => ((Real.logb 2 (memory n) - Weyl.qmdl d 1 s.eigenvalue n : ℝ) : EReal))
      atTop := by
  obtain ⟨z, hz, rfl⟩ := RankOneStates.exists_normalized_vector ρ hρ ht hrank
  exact theorem1_pure_converse s z hz memory E D herror

/-- In particular, the manuscript's uniform reliability criterion implies
the same exact lower bound, without any assumed aggregate-error estimate. -/
theorem theorem1_rank_one_converse_of_uniform (s : FixedSpectrum d 1)
    (ρ : Matrix (Fin d) (Fin d) ℂ) (hρ : ρ.PosSemidef) (ht : ρ.trace = 1)
    (hrank : ρ.rank = 1) (memory : ℕ → ℕ)
    (E : ∀ n, MatrixChannel (Fin n → Fin d) (Fin (memory n)))
    (D : ∀ n, MatrixChannel (Fin (memory n)) (Fin n → Fin d))
    (δ : ℕ → ℝ) (hδ : Tendsto δ atTop (𝓝 0))
    (haccuracy : ∀ᶠ n in atTop, ∀ U,
      traceDistance ((D n).toFun ((E n).toFun (orbitState n ρ U))) (orbitState n ρ U) ≤ δ n) :
    (0 : EReal) ≤ liminf
      (fun n => ((Real.logb 2 (memory n) - Weyl.qmdl d 1 s.eigenvalue n : ℝ) : EReal))
      atTop := by
  have hd : 0 < d := lt_of_lt_of_le s.rank_pos s.rank_le
  apply optimal_memory_converse (γ := 1)
    (targetDim := fun n => Fintype.card (Occupation d n))
    (error := δ) (transferError := fun _ => 0) (by norm_num)
    (fun n => occupationDimension_pos d n hd) hδ tendsto_const_nhds
    (occupation_qmdl_asymptotic s)
  filter_upwards [haccuracy] with n hn
  have he := averageError_le_of_uniform n ρ (E n) (D n) (δ n) hn
  have hb := rank_one_memory_bound n hd ρ hρ ht hrank (E n) (D n)
  have h := (mul_le_mul_of_nonneg_left (sub_le_sub_left he 1)
    (Nat.cast_nonneg (Fintype.card (Occupation d n)))).trans hb
  simpa only [add_zero, div_one, Fintype.card_fin] using h

/-- Theorem 2's concrete rank-one instance for arbitrary density matrices:
the actual forward cloning channel has the proved finite error rate, and
the actual reverse channel reconstructs the smaller tensor power exactly. -/
theorem theorem2_rank_one_cloning (n m : ℕ) (hd : 0 < d)
    (ρ : Matrix (Fin d) (Fin d) ℂ) (hρ : ρ.PosSemidef) (ht : ρ.trace = 1)
    (hrank : ρ.rank = 1) :
    traceDistance ((OccupationCloning.physicalForward d n m hd).toFun (matrix n ρ))
      (matrix (n + m) ρ) ≤ ((d - 1 : ℕ) : ℝ) * m / ((n : ℝ) + 1) ∧
    (OccupationCloning.physicalReverse d n m hd).toFun (matrix (n + m) ρ) = matrix n ρ := by
  obtain ⟨z, hz, rfl⟩ := RankOneStates.exists_normalized_vector ρ hρ ht hrank
  exact OccupationCloning.theorem2_physical_pure_cloning d n m hd z hz

end FreeEntropy.RankOneCompression
