/-
Copyright (c) 2026 Free Entropy formalization contributors.
See LICENSE and NOTICE in the repository root for license and attribution.
-/

import FreeEntropy.OrbitMemory
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Basic
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Abs

/-!
# Concrete matrix trace distance

The trace norm is `Tr sqrt(X†X)`, using mathlib's matrix functional calculus.
The spectral diagonalization argument in `traceNorm_sub_le_trace_add` is adapted
from the local Cloning project's `Cloning/MatrixTraceNormOrder.lean` (read-only
reference); it is reproved here against mathlib with no project dependencies.
-/

open scoped BigOperators MatrixOrder ComplexOrder
open Matrix Unitary
open FreeEntropy.OrbitMemory

namespace FreeEntropy.TraceDistance

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 400000

variable {H M : Type*} [Fintype H] [DecidableEq H] [Fintype M] [DecidableEq M]

/-- The actual matrix trace norm `Tr sqrt(X†X)`. -/
noncomputable def traceNorm (X : Matrix H H ℂ) : ℝ := tr (CFC.abs X)

/-- Half the trace norm of the matrix difference. -/
noncomputable def traceDistance (A B : Matrix H H ℂ) : ℝ := traceNorm (A - B) / 2

@[simp] theorem traceNorm_neg (X : Matrix H H ℂ) : traceNorm (-X) = traceNorm X := by
  simp [traceNorm]

@[simp] theorem traceNorm_zero : traceNorm (0 : Matrix H H ℂ) = 0 := by
  simp [traceNorm, tr]

theorem traceNorm_nonneg (X : Matrix H H ℂ) : 0 ≤ traceNorm X :=
  (CFC.abs_nonneg X).posSemidef.trace_nonneg.1

theorem traceDistance_nonneg (A B : Matrix H H ℂ) : 0 ≤ traceDistance A B :=
  div_nonneg (traceNorm_nonneg _) (by norm_num)

theorem traceNorm_sub_comm (A B : Matrix H H ℂ) : traceNorm (A - B) = traceNorm (B - A) := by
  rw [← traceNorm_neg (B - A), neg_sub]

theorem traceDistance_symm (A B : Matrix H H ℂ) : traceDistance A B = traceDistance B A := by
  rw [traceDistance, traceDistance, traceNorm_sub_comm]

/-- For a Hermitian matrix the trace norm is the sum of absolute eigenvalues. -/
theorem traceNorm_eq_sum_abs_eigenvalues {D : Matrix H H ℂ} (hD : D.IsHermitian) :
    traceNorm D = ∑ i, |hD.eigenvalues i| := by
  rw [traceNorm, tr, CFC.abs_eq_cfc_norm D hD,
    hD.cfc_eq (fun x : ℝ ↦ ‖x‖), Matrix.IsHermitian.cfc, conjStarAlgAut_apply,
    Matrix.trace_mul_cycle, Unitary.coe_star_mul_self, one_mul, Matrix.trace_diagonal]
  simp only [Function.comp_apply, Complex.re_sum, Real.norm_eq_abs]
  apply Finset.sum_congr rfl
  intro i _
  exact RCLike.ofReal_re (K := ℂ) |hD.eigenvalues i|

/-- Any positive decomposition bounds the trace norm. -/
theorem traceNorm_sub_le_trace_add {A B : Matrix H H ℂ}
    (hA : A.PosSemidef) (hB : B.PosSemidef) :
    traceNorm (A - B) ≤ tr A + tr B := by
  let hD : (A - B).IsHermitian := hA.isHermitian.sub hB.isHermitian
  let U := hD.eigenvectorUnitary
  let C : Matrix H H ℂ := (star U : Matrix H H ℂ) * A * (U : Matrix H H ℂ)
  let F : Matrix H H ℂ := (star U : Matrix H H ℂ) * B * (U : Matrix H H ℂ)
  have hC : C.PosSemidef := hA.conjTranspose_mul_mul_same (U : Matrix H H ℂ)
  have hF : F.PosSemidef := hB.conjTranspose_mul_mul_same (U : Matrix H H ℂ)
  have hdiag : C - F = Matrix.diagonal (fun i ↦ (hD.eigenvalues i : ℂ)) := by
    dsimp only [C, F]
    rw [← Matrix.sub_mul, ← Matrix.mul_sub]
    simpa only [conjStarAlgAut_star_apply, Function.comp_apply, Unitary.coe_star] using
      hD.conjStarAlgAut_star_eigenvectorUnitary
  have heig i : hD.eigenvalues i = (C i i).re - (F i i).re := by
    have h := congrArg (fun M : Matrix H H ℂ ↦ (M i i).re) hdiag
    simpa only [Matrix.sub_apply, Complex.sub_re, Matrix.diagonal_apply_eq,
      Complex.ofReal_re] using h.symm
  have htrC : Matrix.trace C = Matrix.trace A := by
    dsimp only [C]
    rw [Matrix.trace_mul_cycle,
      show (U : Matrix H H ℂ) * star (U : Matrix H H ℂ) = 1 from
        Unitary.mul_star_self_of_mem U.property, one_mul]
  have htrF : Matrix.trace F = Matrix.trace B := by
    dsimp only [F]
    rw [Matrix.trace_mul_cycle,
      show (U : Matrix H H ℂ) * star (U : Matrix H H ℂ) = 1 from
        Unitary.mul_star_self_of_mem U.property, one_mul]
  calc
    traceNorm (A - B) = ∑ i, |hD.eigenvalues i| := traceNorm_eq_sum_abs_eigenvalues hD
    _ ≤ ∑ i, ((C i i).re + (F i i).re) := by
      apply Finset.sum_le_sum
      intro i _
      rw [heig i]
      calc
        |(C i i).re - (F i i).re| ≤ |(C i i).re| + |(F i i).re| := abs_sub _ _
        _ = (C i i).re + (F i i).re := by
          rw [abs_of_nonneg (Complex.nonneg_iff.mp (hC.diag_nonneg (i := i))).1,
            abs_of_nonneg (Complex.nonneg_iff.mp (hF.diag_nonneg (i := i))).1]
    _ = tr C + tr F := by
      simp only [tr, Matrix.trace, Matrix.diag, Complex.re_sum, Finset.sum_add_distrib]
    _ = tr A + tr B := by simp only [tr, htrC, htrF]

/-- The Jordan positive and negative parts attain the trace-norm cost. -/
theorem jordan_trace_mass {D : Matrix H H ℂ} (hD : D.IsHermitian) :
    tr D⁺ + tr D⁻ = traceNorm D := by
  rw [← tr_add, CFC.posPart_add_negPart D hD]
  rfl

/-- Testing a positive matrix against an effect cannot exceed its trace. -/
theorem effect_trace_le {P A : Matrix H H ℂ} (hP : P ≤ 1) (hA : A.PosSemidef) :
    tr (P * A) ≤ tr A := by
  have h := trace_mul_mono hA hP
  simpa only [tr, Matrix.trace_mul_comm A P, Matrix.mul_one] using h

/-- A Hermitian matrix of trace zero has equal positive and negative masses. -/
theorem jordan_trace_eq_half {D : Matrix H H ℂ} (hD : D.IsHermitian) (ht : tr D = 0) :
    tr D⁺ = traceNorm D / 2 ∧ tr D⁻ = traceNorm D / 2 := by
  have hmass := jordan_trace_mass hD
  have hdiff := congrArg tr (CFC.posPart_sub_negPart D hD)
  simp only [tr, Matrix.trace_sub, Complex.sub_re] at hdiff
  change tr D⁺ - tr D⁻ = tr D at hdiff
  rw [ht] at hdiff
  constructor <;> linarith

/-- The sharp factor-one-half measurement bound for traceless Hermitian matrices. -/
theorem measurement_bound {P D : Matrix H H ℂ} (hD : D.IsHermitian) (ht : tr D = 0)
    (hP : P.PosSemidef) (hP1 : P ≤ 1) : |tr (P * D)| ≤ traceNorm D / 2 := by
  have hp : D⁺.PosSemidef := (CFC.posPart_nonneg D).posSemidef
  have hn : D⁻.PosSemidef := (CFC.negPart_nonneg D).posSemidef
  have hp0 := trace_mul_nonneg hP hp
  have hn0 := trace_mul_nonneg hP hn
  have hp1 := effect_trace_le hP1 hp
  have hn1 := effect_trace_le hP1 hn
  have hh := jordan_trace_eq_half hD ht
  have hd : tr (P * D) = tr (P * D⁺) - tr (P * D⁻) := by
    conv_lhs => rw [← CFC.posPart_sub_negPart D hD]
    simp only [Matrix.mul_sub, tr, Matrix.trace_sub, Complex.sub_re]
  rw [hd, abs_le]
  constructor <;> linarith

/-- State testing by any effect is bounded by the actual trace distance. -/
theorem state_measurement_bound {P A B : Matrix H H ℂ}
    (hA : A.PosSemidef) (hB : B.PosSemidef) (ht : A.trace = B.trace)
    (hP : P.PosSemidef) (hP1 : P ≤ 1) :
    |tr (P * A) - tr (P * B)| ≤ traceDistance A B := by
  have hz : tr (A - B) = 0 := by simp [tr, Matrix.trace_sub, ht]
  simpa only [traceDistance, Matrix.mul_sub, tr, Matrix.trace_sub, Complex.sub_re] using
    measurement_bound (hA.isHermitian.sub hB.isHermitian) hz hP hP1

/-- An operator remainder bounds both the trace distance and the missing
trace of a retained branch. This is equation `positive_deficit_trace`'s
inequality; positivity of A and trace A ≤ 1 are unnecessary for the bound. -/
theorem positive_remainder_bound {A B R : Matrix H H ℂ}
    (hR : R.PosSemidef) (hle : B - R ≤ A) :
    (traceNorm (A - B) + tr B - tr A) / 2 ≤ tr R := by
  have hS : (A - (B - R)).PosSemidef := Matrix.le_iff.mp hle
  have h := traceNorm_sub_le_trace_add hR hS
  have hid : R - (A - (B - R)) = B - A := by abel
  rw [hid, ← traceNorm_sub_comm A B] at h
  simp only [tr, Matrix.trace_sub, Complex.sub_re] at h
  change traceNorm (A - B) ≤ tr R + (tr A - (tr B - tr R)) at h
  linarith

/-- The retained-branch form for a normalized target. -/
theorem retained_branch_error_bound {A B R : Matrix H H ℂ}
    (hBt : B.trace = 1) (hR : R.PosSemidef) (hle : B - R ≤ A) :
    traceDistance A B + (1 - tr A) / 2 ≤ tr R := by
  have h := positive_remainder_bound hR hle
  have htr : tr B = 1 := by simp [tr, hBt]
  rw [htr] at h
  unfold traceDistance
  linarith

/-- For equal-trace states the remainder directly bounds trace distance. -/
theorem traceDistance_le_remainder {A B R : Matrix H H ℂ}
    (ht : A.trace = B.trace) (hR : R.PosSemidef) (hle : B - R ≤ A) :
    traceDistance A B ≤ tr R := by
  have h := positive_remainder_bound hR hle
  have htr : tr B = tr A := congrArg Complex.re ht.symm
  rw [htr] at h
  simpa [traceDistance] using h

/-- Positive trace-preserving real-linear maps contract the trace norm on
Hermitian inputs; complete positivity is stronger than needed. -/
theorem traceNorm_contract_hermitian
    (E : Matrix H H ℂ →ₗ[ℝ] Matrix M M ℂ)
    (hE : ∀ A, A.PosSemidef → (E A).PosSemidef)
    (hEt : ∀ A, (E A).trace = A.trace)
    {D : Matrix H H ℂ} (hD : D.IsHermitian) : traceNorm (E D) ≤ traceNorm D := by
  have hp := hE D⁺ (CFC.posPart_nonneg D).posSemidef
  have hn := hE D⁻ (CFC.negPart_nonneg D).posSemidef
  have h := traceNorm_sub_le_trace_add hp hn
  rw [← map_sub, CFC.posPart_sub_negPart D hD] at h
  simpa only [tr, hEt, ← jordan_trace_mass hD] using h

theorem traceDistance_contract
    (E : Matrix H H ℂ →ₗ[ℝ] Matrix M M ℂ)
    (hE : ∀ A, A.PosSemidef → (E A).PosSemidef)
    (hEt : ∀ A, (E A).trace = A.trace)
    {A B : Matrix H H ℂ} (hA : A.PosSemidef) (hB : B.PosSemidef) :
    traceDistance (E A) (E B) ≤ traceDistance A B := by
  unfold traceDistance
  rw [← map_sub]
  exact div_le_div_of_nonneg_right
    (traceNorm_contract_hermitian E hE hEt (hA.isHermitian.sub hB.isHermitian)) (by norm_num)

/-- Positive trace-nonincreasing maps also contract the Hermitian trace norm. -/
theorem traceNorm_contract_hermitian_of_trace_le
    (E : Matrix H H ℂ →ₗ[ℝ] Matrix M M ℂ)
    (hE : ∀ A, A.PosSemidef → (E A).PosSemidef)
    (hEt : ∀ A, A.PosSemidef → tr (E A) ≤ tr A)
    {D : Matrix H H ℂ} (hD : D.IsHermitian) : traceNorm (E D) ≤ traceNorm D := by
  have hp : D⁺.PosSemidef := (CFC.posPart_nonneg D).posSemidef
  have hn : D⁻.PosSemidef := (CFC.negPart_nonneg D).posSemidef
  have h := traceNorm_sub_le_trace_add (hE _ hp) (hE _ hn)
  rw [← map_sub, CFC.posPart_sub_negPart D hD] at h
  exact h.trans ((add_le_add (hEt _ hp) (hEt _ hn)).trans_eq (jordan_trace_mass hD))

theorem traceDistance_contract_of_trace_le
    (E : Matrix H H ℂ →ₗ[ℝ] Matrix M M ℂ)
    (hE : ∀ A, A.PosSemidef → (E A).PosSemidef)
    (hEt : ∀ A, A.PosSemidef → tr (E A) ≤ tr A)
    {A B : Matrix H H ℂ} (hA : A.PosSemidef) (hB : B.PosSemidef) :
    traceDistance (E A) (E B) ≤ traceDistance A B := by
  unfold traceDistance
  rw [← map_sub]
  exact div_le_div_of_nonneg_right
    (traceNorm_contract_hermitian_of_trace_le E hE hEt (hA.isHermitian.sub hB.isHermitian))
    (by norm_num)

/-- Rectangular matrix conjugation as a real-linear map. -/
noncomputable def sandwich (V : Matrix M H ℂ) : Matrix H H ℂ →ₗ[ℝ] Matrix M M ℂ where
  toFun X := V * X * Vᴴ
  map_add' X Y := by simp [Matrix.mul_add, Matrix.add_mul]
  map_smul' r X := by simp [Matrix.mul_smul, Matrix.smul_mul]

omit [DecidableEq H] [Fintype M] [DecidableEq M] in
@[simp] theorem sandwich_apply (V : Matrix M H ℂ) (X : Matrix H H ℂ) :
    sandwich V X = V * X * Vᴴ := rfl

omit [DecidableEq M] in
/-- A rectangular contraction induces a trace-nonincreasing positive map. -/
theorem sandwich_trace_le (V : Matrix M H ℂ) (hV : Vᴴ * V ≤ 1)
    {A : Matrix H H ℂ} (hA : A.PosSemidef) : tr (sandwich V A) ≤ tr A := by
  change (V * A * Vᴴ).trace.re ≤ tr A
  rw [Matrix.trace_mul_cycle]
  exact effect_trace_le hV hA

theorem sandwich_traceNorm_le (V : Matrix M H ℂ) (hV : Vᴴ * V ≤ 1)
    {D : Matrix H H ℂ} (hD : D.IsHermitian) :
    traceNorm (V * D * Vᴴ) ≤ traceNorm D :=
  traceNorm_contract_hermitian_of_trace_le (sandwich V)
    (fun _ hA => hA.mul_mul_conjTranspose_same V)
    (fun _ hA => sandwich_trace_le V hV hA) hD

/-- The range projection of a rectangular isometry is an effect. -/
theorem isometry_range_le_one (V : Matrix M H ℂ) (hV : Vᴴ * V = 1) : V * Vᴴ ≤ 1 := by
  have hid : (V * Vᴴ) * (V * Vᴴ) = V * Vᴴ := by
    calc
      _ = V * (Vᴴ * V) * Vᴴ := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [hV]; simp
  have hherm : (V * Vᴴ)ᴴ = V * Vᴴ := by simp
  have hp := Matrix.posSemidef_conjTranspose_mul_self (1 - V * Vᴴ)
  apply Matrix.le_iff.mpr
  simpa only [Matrix.conjTranspose_sub, Matrix.conjTranspose_one, hherm,
    Matrix.mul_sub, Matrix.sub_mul, Matrix.one_mul, Matrix.mul_one, hid,
    sub_self, sub_zero] using hp

/-- Isometric embeddings preserve the actual trace norm of Hermitian matrices. -/
theorem traceNorm_isometry (V : Matrix M H ℂ) (hV : Vᴴ * V = 1)
    {D : Matrix H H ℂ} (hD : D.IsHermitian) :
    traceNorm (V * D * Vᴴ) = traceNorm D := by
  apply le_antisymm (sandwich_traceNorm_le V hV.le hD)
  have hV' : (Vᴴ)ᴴ * Vᴴ ≤ 1 := by
    simpa using isometry_range_le_one V hV
  have h := sandwich_traceNorm_le Vᴴ hV'
    (Matrix.isHermitian_mul_mul_conjTranspose V hD)
  have hid : Vᴴ * (V * D * Vᴴ) * (Vᴴ)ᴴ = D := by
    simp only [Matrix.conjTranspose_conjTranspose]
    calc
      _ = (Vᴴ * V) * D * (Vᴴ * V) := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [hV]; simp
  rwa [hid] at h

/-- The actual trace distance is unchanged by a rectangular isometry. -/
theorem traceDistance_isometry (V : Matrix M H ℂ) (hV : Vᴴ * V = 1)
    {A B : Matrix H H ℂ} (hA : A.PosSemidef) (hB : B.PosSemidef) :
    traceDistance (V * A * Vᴴ) (V * B * Vᴴ) = traceDistance A B := by
  unfold traceDistance
  rw [← Matrix.sub_mul, ← Matrix.mul_sub,
    traceNorm_isometry V hV (hA.isHermitian.sub hB.isHermitian)]

section Continuity

open scoped Matrix.Norms.L2Operator

/-- The concrete trace norm is continuous, including at singular matrices. -/
theorem continuous_traceNorm : Continuous (traceNorm : Matrix H H ℂ → ℝ) := by
  letI : CStarAlgebra (Matrix H H ℂ) := {}
  have htr : Continuous (tr : Matrix H H ℂ → ℝ) :=
    (LinearMap.toContinuousLinearMap
      (Complex.reCLM.toLinearMap.comp (Matrix.traceLinearMap H ℝ ℂ))).continuous
  exact htr.comp CFC.continuous_abs

theorem continuous_traceDistance :
    Continuous (fun p : Matrix H H ℂ × Matrix H H ℂ => traceDistance p.1 p.2) := by
  exact (continuous_traceNorm.comp (continuous_fst.sub continuous_snd)).div_const 2

end Continuity

end FreeEntropy.TraceDistance
