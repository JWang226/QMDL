/-
Copyright (c) 2026 Free Entropy formalization contributors.
See LICENSE and NOTICE in the repository root for license and attribution.
-/

import FreeEntropy.TraceDistance
import FreeEntropy.CloningMatrices

/-!
# Triangle and convexity bounds for actual quantum trace distance

These are proved from positive/negative spectral parts, without assuming
an abstract metric instance for the matrix trace norm.
-/

noncomputable section
open scoped BigOperators MatrixOrder ComplexOrder
open Matrix FreeEntropy.OrbitMemory
namespace FreeEntropy.TraceDistance
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false

variable {H ι : Type*} [Fintype H] [DecidableEq H]

theorem traceNorm_add_le {X Y : Matrix H H ℂ} (hX : X.IsHermitian) (hY : Y.IsHermitian) :
    traceNorm (X + Y) ≤ traceNorm X + traceNorm Y := by
  have h := traceNorm_sub_le_trace_add
    ((CFC.posPart_nonneg X).posSemidef.add (CFC.posPart_nonneg Y).posSemidef)
    ((CFC.negPart_nonneg X).posSemidef.add (CFC.negPart_nonneg Y).posSemidef)
  have hid : (X⁺ + Y⁺) - (X⁻ + Y⁻) = X + Y := by
    calc
      _ = (X⁺ - X⁻) + (Y⁺ - Y⁻) := by abel
      _ = _ := by rw [CFC.posPart_sub_negPart X hX, CFC.posPart_sub_negPart Y hY]
  rw [hid, tr_add, tr_add] at h
  have hx := jordan_trace_mass hX
  have hy := jordan_trace_mass hY
  linarith

theorem traceDistance_triangle {A B C : Matrix H H ℂ}
    (hA : A.IsHermitian) (hB : B.IsHermitian) (hC : C.IsHermitian) :
    traceDistance A C ≤ traceDistance A B + traceDistance B C := by
  have h := traceNorm_add_le (hA.sub hB) (hB.sub hC)
  rw [sub_add_sub_cancel] at h
  unfold traceDistance
  linarith

/-- A finite weighted sum of Hermitian matrices obeys the trace-norm
convexity bound. The weights need not sum to one. -/
theorem traceNorm_weighted_sum_le (s : Finset ι) (w : ι → ℝ) (X : ι → Matrix H H ℂ)
    (hw : ∀ i ∈ s, 0 ≤ w i) (hX : ∀ i ∈ s, (X i).IsHermitian) :
    traceNorm (∑ i ∈ s, w i • X i) ≤ ∑ i ∈ s, w i * traceNorm (X i) := by
  let A := ∑ i ∈ s, w i • (X i)⁺
  let B := ∑ i ∈ s, w i • (X i)⁻
  have hA : A.PosSemidef := Matrix.posSemidef_sum _
    (fun i hi => (CFC.posPart_nonneg (X i)).posSemidef.smul (hw i hi))
  have hB : B.PosSemidef := Matrix.posSemidef_sum _
    (fun i hi => (CFC.negPart_nonneg (X i)).posSemidef.smul (hw i hi))
  have hid : A - B = ∑ i ∈ s, w i • X i := by
    dsimp [A, B]
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    rw [← smul_sub, CFC.posPart_sub_negPart (X i) (hX i hi)]
  have h := traceNorm_sub_le_trace_add hA hB
  rw [hid] at h
  have hmass : tr A + tr B = ∑ i ∈ s, w i * traceNorm (X i) := by
    dsimp only [A, B]
    simp only [tr, Matrix.trace_sum, Matrix.trace_smul, Complex.re_sum, Complex.real_smul,
      Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    have hm := jordan_trace_mass (hX i hi)
    change w i * tr (X i)⁺ + w i * tr (X i)⁻ = _
    rw [← mul_add, hm]
  exact h.trans_eq hmass

/-- Joint convexity for actual trace distances of finite mixtures. -/
theorem traceDistance_mixtures_le (s : Finset ι) (w : ι → ℝ)
    (A B : ι → Matrix H H ℂ) (hw : ∀ i ∈ s, 0 ≤ w i)
    (hA : ∀ i ∈ s, (A i).IsHermitian) (hB : ∀ i ∈ s, (B i).IsHermitian) :
    traceDistance (CloningMatrices.mixture s w A) (CloningMatrices.mixture s w B) ≤
      ∑ i ∈ s, w i * traceDistance (A i) (B i) := by
  unfold traceDistance CloningMatrices.mixture
  rw [← Finset.sum_sub_distrib]
  simp only [← smul_sub]
  have h := traceNorm_weighted_sum_le s w (fun i => A i - B i) hw (fun i hi => (hA i hi).sub (hB i hi))
  have hd := div_le_div_of_nonneg_right h (by norm_num : (0 : ℝ) ≤ 2)
  simpa only [Finset.sum_div, mul_div_assoc] using hd

/-- Convexity with a common reference state. -/
theorem traceDistance_mixture_le (s : Finset ι) (w : ι → ℝ)
    (A : ι → Matrix H H ℂ) (B : Matrix H H ℂ)
    (hw : ∀ i ∈ s, 0 ≤ w i) (hsum : ∑ i ∈ s, w i = 1)
    (hA : ∀ i ∈ s, (A i).IsHermitian) (hB : B.IsHermitian) :
    traceDistance (CloningMatrices.mixture s w A) B ≤ ∑ i ∈ s, w i * traceDistance (A i) B := by
  have hid : CloningMatrices.mixture s w (fun _ => B) = B := by
    rw [CloningMatrices.mixture, ← Finset.sum_smul, hsum, one_smul]
  simpa only [hid] using traceDistance_mixtures_le s w A (fun _ => B) hw hA (fun _ _ => hB)

/-- The maximal distance between normalized positive matrices is one. -/
theorem traceDistance_states_le_one {A B : Matrix H H ℂ}
    (hA : A.PosSemidef) (hB : B.PosSemidef) (hAt : A.trace = 1) (hBt : B.trace = 1) :
    traceDistance A B ≤ 1 := by
  have h := traceNorm_sub_le_trace_add hA hB
  simp only [tr, hAt, hBt, Complex.one_re] at h
  unfold traceDistance
  linarith

end FreeEntropy.TraceDistance
