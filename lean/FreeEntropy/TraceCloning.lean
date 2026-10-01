/-
Copyright (c) 2026 Free Entropy formalization contributors.
See LICENSE and NOTICE in the repository root for license and attribution.
-/

import FreeEntropy.CloningMatrices
import FreeEntropy.WeylFiniteSupplement

/-!
# Cloning from traced projector deficits

Only the traces of the positive block deficits are needed to bound the
trace distance. This avoids the equal-rank operator-norm comparison: a
Casimir bound on the reverse trace transfers to the forward trace by
cyclicity when the shallow multiplicities agree.
-/

noncomputable section
open scoped BigOperators MatrixOrder ComplexOrder
open Matrix FreeEntropy.OrbitMemory FreeEntropy.TraceDistance
open FreeEntropy.CloningMatrices
namespace FreeEntropy.TraceCloning
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 400000

variable {H K ι : Type*} [Fintype H] [DecidableEq H] [Fintype K] [DecidableEq K]

/-- The exact positive block remainders, rather than scalar multiples of
projections, suffice for the channel error estimate. -/
theorem traceDistance_le_traced_loss (s : Finset ι) (p e : ι → ℝ)
    (P C : ι → Matrix H H ℂ) (σ : Matrix H H ℂ) (a : ℝ)
    (hp : ∀ i ∈ s, 0 ≤ p i) (hP : ∀ i ∈ s, (P i).PosSemidef)
    (ha : 0 ≤ a) (ha1 : a ≤ 1)
    (htarget : (mixture s p P).trace = 1) (hσ : σ.trace = 1)
    (hdef : ∀ i ∈ s, (P i - C i).PosSemidef)
    (htrace : ∀ i ∈ s, tr (P i - C i) ≤ e i * tr (P i))
    (hbranch : a • mixture s p C ≤ σ) :
    traceDistance σ (mixture s p P) ≤ 1 - a + ∑ i ∈ s, e i * p i * tr (P i) := by
  let τ := mixture s p P
  let S := mixture s p (fun i => P i - C i)
  let R := (1 - a) • τ + a • S
  have hτ : τ.PosSemidef := mixture_positive s p P hp hP
  have hS : S.PosSemidef := mixture_positive s p _ hp hdef
  have hR : R.PosSemidef := (hτ.smul (sub_nonneg.mpr ha1)).add (hS.smul ha)
  have hblocks : τ - S = mixture s p C := by
    dsimp [τ, S, mixture]
    simp only [smul_sub, Finset.sum_sub_distrib, sub_sub_cancel]
  have hrem : τ - R ≤ σ := by
    have hid : τ - R = a • (τ - S) := by dsimp [R]; module
    rw [hid, hblocks]
    exact hbranch
  have hdist := traceDistance_le_remainder (hσ.trans htarget.symm) hR hrem
  have htrτ : tr τ = 1 := by simp [τ, tr, htarget]
  have hS0 : 0 ≤ tr S := hS.trace_nonneg.1
  have htrS : tr S ≤ ∑ i ∈ s, e i * p i * tr (P i) := by
    dsimp only [S]
    rw [mixture_trace]
    apply Finset.sum_le_sum
    intro i hi
    have h := mul_le_mul_of_nonneg_left (htrace i hi) (hp i hi)
    convert h using 1
    ring
  have htrR : tr R ≤ 1 - a + tr S := by
    dsimp only [R]
    rw [tr_add, tr_smul, tr_smul, htrτ, mul_one]
    nlinarith
  linarith

/-- A retained branch with larger coefficients can be reduced to the target
coefficients before applying the exact traced-deficit bound. -/
theorem forward_traceDistance_le_traced_loss (s : Finset ι) (p q e : ι → ℝ)
    (P C : ι → Matrix H H ℂ) (σ : Matrix H H ℂ) (a : ℝ)
    (hp : ∀ i ∈ s, 0 ≤ p i) (hpq : ∀ i ∈ s, p i ≤ q i)
    (hP : ∀ i ∈ s, (P i).PosSemidef) (hC : ∀ i ∈ s, (C i).PosSemidef)
    (ha : 0 ≤ a) (ha1 : a ≤ 1)
    (htarget : (mixture s p P).trace = 1) (hσ : σ.trace = 1)
    (hdef : ∀ i ∈ s, (P i - C i).PosSemidef)
    (htrace : ∀ i ∈ s, tr (P i - C i) ≤ e i * tr (P i))
    (hbranch : a • mixture s q C ≤ σ) :
    traceDistance σ (mixture s p P) ≤ 1 - a + ∑ i ∈ s, e i * p i * tr (P i) := by
  apply traceDistance_le_traced_loss s p e P C σ a hp hP ha ha1 htarget hσ hdef htrace
  apply le_trans (smul_mono ?_ ha) hbranch
  exact Finset.sum_le_sum fun i hi => coefficient_mono (hC i hi) (hpq i hi)

structure TraceBlockRealization (s : Finset ι) (m n : ι → ℕ)
    (pμ pν e : ι → ℝ) (a : ℝ) (H K : Type*)
    [Fintype H] [DecidableEq H] [Fintype K] [DecidableEq K] where
  Pμ : ι → Matrix H H ℂ
  Pν : ι → Matrix K K ℂ
  Cμ : ι → Matrix H H ℂ
  Cν : ι → Matrix K K ℂ
  forward : Channels.MatrixChannel H K
  reverse : Channels.MatrixChannel K H
  positive_μ : ∀ i ∈ s, (Pμ i).PosSemidef
  positive_ν : ∀ i ∈ s, (Pν i).PosSemidef
  compressed_positive_ν : ∀ i ∈ s, (Cν i).PosSemidef
  trace_μ : ∀ i ∈ s, tr (Pμ i) = (m i : ℝ)
  trace_ν : ∀ i ∈ s, tr (Pν i) = (n i : ℝ)
  normalized_μ : (mixture s pμ Pμ).trace = 1
  normalized_ν : (mixture s pν Pν).trace = 1
  deficit_positive_μ : ∀ i ∈ s, (Pμ i - Cμ i).PosSemidef
  deficit_positive_ν : ∀ i ∈ s, (Pν i - Cν i).PosSemidef
  deficit_trace_μ : ∀ i ∈ s, tr (Pμ i - Cμ i) ≤ e i * tr (Pμ i)
  deficit_trace_ν : ∀ i ∈ s, tr (Pν i - Cν i) ≤ e i * tr (Pν i)
  branch_forward : a • mixture s pμ Cν ≤ forward.toFun (mixture s pμ Pμ)
  branch_reverse : mixture s pν Cμ ≤ reverse.toFun (mixture s pν Pν)

/-- The former `hf` and `hr` hypotheses now follow for concrete CPTP
outputs from the finite block geometry. -/
theorem TraceBlockRealization.error_comparisons
    {s : Finset ι} {m n : ι → ℕ} {pμ pν e : ι → ℝ} {a Z : ℝ}
    (R : TraceBlockRealization s m n pμ pν e a H K)
    (hpμ : ∀ i ∈ s, 0 ≤ pμ i) (hpν : ∀ i ∈ s, 0 ≤ pν i)
    (ha : 0 ≤ a) (ha1 : a ≤ 1)
    (hZ : 0 ≤ Z) (hZ1 : Z ≤ 1) (hratio : ∀ i ∈ s, pν i = Z * pμ i) :
    traceDistance (R.forward.toFun (mixture s pμ R.Pμ)) (mixture s pν R.Pν) ≤
        1 - a + ∑ i ∈ s, e i * (pν i * (n i : ℝ)) ∧
    traceDistance (R.reverse.toFun (mixture s pν R.Pν)) (mixture s pμ R.Pμ) ≤
        1 - Z + ∑ i ∈ s, e i * (pμ i * (m i : ℝ)) := by
  have hf := forward_traceDistance_le_traced_loss s pν pμ e R.Pν R.Cν
    (R.forward.toFun (mixture s pμ R.Pμ)) a hpν
    (fun i hi => by rw [hratio i hi]; nlinarith [hpμ i hi])
    R.positive_ν R.compressed_positive_ν ha ha1 R.normalized_ν
    ((R.forward.trace_preserving _).trans R.normalized_μ) R.deficit_positive_ν R.deficit_trace_ν R.branch_forward
  have hbranch : Z • mixture s pμ R.Cμ ≤ R.reverse.toFun (mixture s pν R.Pν) := by
    have hid : Z • mixture s pμ R.Cμ = mixture s pν R.Cμ := by
      unfold mixture
      rw [Finset.smul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      rw [smul_smul, hratio i hi]
    rw [hid]
    exact R.branch_reverse
  have hr := traceDistance_le_traced_loss s pμ e R.Pμ R.Cμ
    (R.reverse.toFun (mixture s pν R.Pν)) Z hpμ R.positive_μ hZ hZ1
    R.normalized_μ ((R.reverse.trace_preserving _).trans R.normalized_ν) R.deficit_positive_μ R.deficit_trace_μ hbranch
  constructor
  · convert hf using 1
    congr 1
    apply Finset.sum_congr rfl
    intro i hi
    rw [R.trace_ν i hi, mul_assoc]
  · convert hr using 1
    congr 1
    apply Finset.sum_congr rfl
    intro i hi
    rw [R.trace_μ i hi, mul_assoc]

/-- Theorem 2 for actual channel outputs. The error comparisons and the
zero-difference channel-error identity are derived, not hypothesized.
Remaining inputs concern representation weights, block geometry, and the
Weyl dimension formula (the latter can use `WeylFinite`). -/
theorem theorem2_of_traced_blocks (s : Finset ι)
    (depth m n : ι → ℕ) (pμ pν : ι → ℝ) (d r D g : ℕ)
    (b q a Z : ℝ)
    (R : TraceBlockRealization s m n pμ pν
      (fun i => min 1 (2 * (depth i : ℝ) * (D : ℝ) / ((g : ℝ) + 2))) a H K)
    (hrank : 2 ≤ r) (hq : 0 ≤ q) (hq1 : q < 1)
    (hb : 0 ≤ b) (hbg : b ≤ (g : ℝ)) (ha : 0 ≤ a) (ha1 : a ≤ 1)
    (hpμ : ∀ i ∈ s, 0 ≤ pμ i) (hpν : ∀ i ∈ s, 0 ≤ pν i)
    (hmn : ∀ i ∈ s, m i ≤ n i)
    (hshallow : ∀ i ∈ s, depth i ≤ g → m i = n i)
    (hzero_mult : D = 0 → ∀ i ∈ s, m i = n i)
    (hratio : ∀ i ∈ s, pν i = Z * pμ i)
    (hμ_spectral : ∀ i ∈ s, pμ i ≤ q ^ depth i)
    (hν_spectral : ∀ i ∈ s, pν i ≤ q ^ depth i)
    (hμ_mult : ∀ t, ∑ i ∈ s with depth i = t, m i ≤
      (t + r.choose 2 - 1).choose (r.choose 2 - 1))
    (hν_mult : ∀ t, ∑ i ∈ s with depth i = t, n i ≤
      (t + r.choose 2 - 1).choose (r.choose 2 - 1))
    (hdim : 1 - a ≤ (d.choose 2 : ℝ) * (D : ℝ) / (b + 1)) :
    traceDistance (R.forward.toFun (mixture s pμ R.Pμ)) (mixture s pν R.Pν) ≤
        Theorem2.cloningConstant d r q * (D : ℝ) / (b + 1) ∧
    traceDistance (R.reverse.toFun (mixture s pν R.Pν)) (mixture s pμ R.Pμ) ≤
        Theorem2.cloningConstant d r q * (D : ℝ) / (b + 1) := by
  have hμ_norm : ∑ i ∈ s, pμ i * (m i : ℝ) = 1 := by
    have ht : tr (mixture s pμ R.Pμ) = 1 := by simp [tr, R.normalized_μ]
    rw [mixture_trace] at ht
    convert ht using 1
    apply Finset.sum_congr rfl
    intro i hi
    rw [R.trace_μ i hi]
  have hν_norm : ∑ i ∈ s, pν i * (n i : ℝ) = 1 := by
    have ht : tr (mixture s pν R.Pν) = 1 := by simp [tr, R.normalized_ν]
    rw [mixture_trace] at ht
    convert ht using 1
    apply Finset.sum_congr rfl
    intro i hi
    rw [R.trace_ν i hi]
  obtain ⟨hZ, hZ1⟩ := ratio_interval s m n pμ pν Z hpν hmn hμ_norm hν_norm hratio
  obtain ⟨hf, hr⟩ := R.error_comparisons hpμ hpν ha ha1 hZ hZ1 hratio
  apply Theorem2.theorem2_finite_reduction s depth m n pμ pν d r D g b q _ _ a Z
    hrank hq hq1 hb hbg hpμ hpν hmn hshallow hμ_norm hν_norm hratio
    hμ_spectral hν_spectral hμ_mult hν_mult hdim ?_ hf hr
  intro hD
  have hZeq : Z = 1 := by
    have hm_norm : ∑ i ∈ s, pν i * (m i : ℝ) = 1 := by
      convert hν_norm using 1
      apply Finset.sum_congr rfl
      intro i hi
      rw [hzero_mult hD i hi]
    calc
      Z = Z * (∑ i ∈ s, pμ i * (m i : ℝ)) := by rw [hμ_norm, mul_one]
      _ = ∑ i ∈ s, pν i * (m i : ℝ) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i hi
        rw [hratio i hi, mul_assoc]
      _ = 1 := hm_norm
  simp only [hD, Nat.cast_zero, mul_zero, zero_div, min_eq_right (by norm_num : (0 : ℝ) ≤ 1),
    zero_mul, Finset.sum_const_zero, add_zero] at hf hr hdim
  constructor
  · exact le_antisymm (hf.trans hdim) (traceDistance_nonneg _ _)
  · rw [hZeq, sub_self] at hr
    exact le_antisymm hr (traceDistance_nonneg _ _)


end FreeEntropy.TraceCloning
