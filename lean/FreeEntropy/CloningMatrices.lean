/-
Copyright (c) 2026 Free Entropy formalization contributors.
See LICENSE and NOTICE in the repository root for license and attribution.
-/

import FreeEntropy.TraceDistance
import FreeEntropy.Theorem2
import FreeEntropy.Channels

/-!
# The cloning error comparison for actual matrices

The positive remainders are constructed explicitly from the weight blocks.
Thus the forward and reverse scalar error comparisons in `Theorem2` follow
from matrix compression and retained-branch inequalities. They are no longer
assumptions about an otherwise uninterpreted error variable.
-/

noncomputable section
open scoped BigOperators MatrixOrder ComplexOrder
open Matrix FreeEntropy.OrbitMemory FreeEntropy.TraceDistance

namespace FreeEntropy.CloningMatrices
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 400000
set_option linter.unusedSectionVars false

variable {H ι : Type*} [Fintype H] [DecidableEq H]

def mixture (s : Finset ι) (p : ι → ℝ) (P : ι → Matrix H H ℂ) : Matrix H H ℂ :=
  ∑ i ∈ s, p i • P i

theorem mixture_positive (s : Finset ι) (p : ι → ℝ) (P : ι → Matrix H H ℂ)
    (hp : ∀ i ∈ s, 0 ≤ p i) (hP : ∀ i ∈ s, (P i).PosSemidef) :
    (mixture s p P).PosSemidef := by
  apply Matrix.posSemidef_sum
  intro i hi
  exact (hP i hi).smul (hp i hi)

theorem mixture_trace (s : Finset ι) (p : ι → ℝ) (P : ι → Matrix H H ℂ) :
    tr (mixture s p P) = ∑ i ∈ s, p i * tr (P i) := by
  simp [mixture, tr, Matrix.trace_sum, Matrix.trace_smul, Complex.re_sum]

theorem smul_mono {A B : Matrix H H ℂ} (h : A ≤ B) {a : ℝ} (ha : 0 ≤ a) :
    a • A ≤ a • B := by
  apply Matrix.le_iff.mpr
  simpa only [smul_sub] using (Matrix.le_iff.mp h).smul ha

theorem coefficient_mono {A : Matrix H H ℂ} (hA : A.PosSemidef)
    {a b : ℝ} (hab : a ≤ b) : a • A ≤ b • A := by
  apply Matrix.le_iff.mpr
  simpa only [sub_smul] using hA.smul (sub_nonneg.mpr hab)

/-- An explicit positive remainder bounds the error of a retained block
mixture. The loss `1-a` and the averaged block deficits are derived here. -/
theorem traceDistance_le_block_loss (s : Finset ι) (p e : ι → ℝ)
    (P C : ι → Matrix H H ℂ) (σ : Matrix H H ℂ) (a : ℝ)
    (hp : ∀ i ∈ s, 0 ≤ p i) (he : ∀ i ∈ s, 0 ≤ e i)
    (hP : ∀ i ∈ s, (P i).PosSemidef)
    (ha : 0 ≤ a) (ha1 : a ≤ 1)
    (htarget : (mixture s p P).trace = 1) (hσ : σ.trace = 1)
    (hblock : ∀ i ∈ s, (1 - e i) • P i ≤ C i)
    (hbranch : a • mixture s p C ≤ σ) :
    traceDistance σ (mixture s p P) ≤ 1 - a + ∑ i ∈ s, e i * p i * tr (P i) := by
  let τ := mixture s p P
  let S := mixture s (fun i => e i * p i) P
  let R := (1 - a) • τ + a • S
  have hτ : τ.PosSemidef := mixture_positive s p P hp hP
  have hS : S.PosSemidef := mixture_positive s _ P
    (fun i hi => mul_nonneg (he i hi) (hp i hi)) hP
  have hR : R.PosSemidef := (hτ.smul (sub_nonneg.mpr ha1)).add (hS.smul ha)
  have hblocks : τ - S ≤ mixture s p C := by
    dsimp [τ, S, mixture]
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_le_sum
    intro i hi
    have h := smul_mono (hblock i hi) (hp i hi)
    simpa only [sub_smul, one_smul, smul_sub, smul_smul, mul_comm] using h
  have hrem : τ - R ≤ σ := by
    have hid : τ - R = a • (τ - S) := by
      dsimp [R]
      module
    rw [hid]
    exact (smul_mono hblocks ha).trans hbranch
  have hdist := traceDistance_le_remainder (hσ.trans htarget.symm) hR hrem
  have htrτ : tr τ = 1 := by simp [τ, tr, htarget]
  have htrS : tr S = ∑ i ∈ s, e i * p i * tr (P i) := mixture_trace s _ P
  have hS0 : 0 ≤ tr S := hS.trace_nonneg.1
  have htrace : tr R ≤ 1 - a + tr S := by
    dsimp only [R]
    rw [tr_add, tr_smul, tr_smul, htrτ, mul_one]
    nlinarith
  exact hdist.trans (by simpa only [htrS] using htrace)

/-- The forward comparison also allows the retained source coefficients to
be larger than the target coefficients, as in `pν = Z pμ`, `Z ≤ 1`. -/
theorem forward_traceDistance_le (s : Finset ι) (p q e : ι → ℝ)
    (P C : ι → Matrix H H ℂ) (σ : Matrix H H ℂ) (a : ℝ)
    (hp : ∀ i ∈ s, 0 ≤ p i) (he : ∀ i ∈ s, 0 ≤ e i)
    (hpq : ∀ i ∈ s, p i ≤ q i)
    (hP : ∀ i ∈ s, (P i).PosSemidef) (hC : ∀ i ∈ s, (C i).PosSemidef)
    (ha : 0 ≤ a) (ha1 : a ≤ 1)
    (htarget : (mixture s p P).trace = 1) (hσ : σ.trace = 1)
    (hblock : ∀ i ∈ s, (1 - e i) • P i ≤ C i)
    (hbranch : a • mixture s q C ≤ σ) :
    traceDistance σ (mixture s p P) ≤ 1 - a + ∑ i ∈ s, e i * p i * tr (P i) := by
  apply traceDistance_le_block_loss s p e P C σ a hp he hP ha ha1 htarget hσ hblock
  apply le_trans (smul_mono ?_ ha) hbranch
  apply Finset.sum_le_sum
  intro i hi
  exact coefficient_mono (hC i hi) (hpq i hi)

/-- The eigenvalue scaling lies in `[0,1]`, purely from normalized block
traces and multiplicity monotonicity. -/
theorem ratio_interval (s : Finset ι) (m n : ι → ℕ) (p q : ι → ℝ) (Z : ℝ)
    (hq : ∀ i ∈ s, 0 ≤ q i) (hmn : ∀ i ∈ s, m i ≤ n i)
    (hp_norm : ∑ i ∈ s, p i * (m i : ℝ) = 1)
    (hq_norm : ∑ i ∈ s, q i * (n i : ℝ) = 1)
    (hratio : ∀ i ∈ s, q i = Z * p i) : 0 ≤ Z ∧ Z ≤ 1 := by
  have hid : ∑ i ∈ s, q i * (m i : ℝ) = Z := by
    calc
      _ = ∑ i ∈ s, Z * (p i * (m i : ℝ)) := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [hratio i hi, mul_assoc]
      _ = Z := by rw [← Finset.mul_sum, hp_norm, mul_one]
  constructor
  · rw [← hid]
    exact Finset.sum_nonneg fun i hi => mul_nonneg (hq i hi) (Nat.cast_nonneg _)
  · rw [← hid, ← hq_norm]
    exact Finset.sum_le_sum fun i hi => mul_le_mul_of_nonneg_left
      (by exact_mod_cast hmn i hi) (hq i hi)

variable {K : Type*} [Fintype K] [DecidableEq K]

/-- The remaining finite block geometry, stated using actual matrices and
CPTP maps. `Cμ` and `Cν` are compressed projector blocks. The branch fields
follow from CartanChannel's retained-branch theorems once the weight-block
decompositions of the representation states are constructed. No error
estimate or zero-error conclusion is a field of this structure. -/
structure BlockRealization (s : Finset ι) (m n : ι → ℕ)
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
  block_μ : ∀ i ∈ s, (1 - e i) • Pμ i ≤ Cμ i
  block_ν : ∀ i ∈ s, (1 - e i) • Pν i ≤ Cν i
  branch_forward : a • mixture s pμ Cν ≤ forward.toFun (mixture s pμ Pμ)
  branch_reverse : mixture s pν Cμ ≤ reverse.toFun (mixture s pν Pν)

/-- The former `hf` and `hr` hypotheses now follow for concrete CPTP
outputs from the finite block geometry. -/
theorem BlockRealization.error_comparisons
    {s : Finset ι} {m n : ι → ℕ} {pμ pν e : ι → ℝ} {a Z : ℝ}
    (R : BlockRealization s m n pμ pν e a H K)
    (hpμ : ∀ i ∈ s, 0 ≤ pμ i) (hpν : ∀ i ∈ s, 0 ≤ pν i)
    (he : ∀ i ∈ s, 0 ≤ e i) (ha : 0 ≤ a) (ha1 : a ≤ 1)
    (hZ : 0 ≤ Z) (hZ1 : Z ≤ 1) (hratio : ∀ i ∈ s, pν i = Z * pμ i) :
    traceDistance (R.forward.toFun (mixture s pμ R.Pμ)) (mixture s pν R.Pν) ≤
        1 - a + ∑ i ∈ s, e i * (pν i * (n i : ℝ)) ∧
    traceDistance (R.reverse.toFun (mixture s pν R.Pν)) (mixture s pμ R.Pμ) ≤
        1 - Z + ∑ i ∈ s, e i * (pμ i * (m i : ℝ)) := by
  have hf := forward_traceDistance_le s pν pμ e R.Pν R.Cν
    (R.forward.toFun (mixture s pμ R.Pμ)) a hpν he
    (fun i hi => by rw [hratio i hi]; nlinarith [hpμ i hi])
    R.positive_ν R.compressed_positive_ν ha ha1 R.normalized_ν
    ((R.forward.trace_preserving _).trans R.normalized_μ) R.block_ν R.branch_forward
  have hbranch : Z • mixture s pμ R.Cμ ≤ R.reverse.toFun (mixture s pν R.Pν) := by
    have hid : Z • mixture s pμ R.Cμ = mixture s pν R.Cμ := by
      unfold mixture
      rw [Finset.smul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      rw [smul_smul, hratio i hi]
    rw [hid]
    exact R.branch_reverse
  have hr := traceDistance_le_block_loss s pμ e R.Pμ R.Cμ
    (R.reverse.toFun (mixture s pν R.Pν)) Z hpμ he R.positive_μ hZ hZ1
    R.normalized_μ ((R.reverse.trace_preserving _).trans R.normalized_ν) R.block_μ hbranch
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
theorem theorem2_of_block_realization (s : Finset ι)
    (depth m n : ι → ℕ) (pμ pν : ι → ℝ) (d r D g : ℕ)
    (b q a Z : ℝ)
    (R : BlockRealization s m n pμ pν
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
  obtain ⟨hf, hr⟩ := R.error_comparisons hpμ hpν
    (fun i _ => le_min (by norm_num) (by positivity)) ha ha1 hZ hZ1 hratio
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

/-- Rank-one spectrum case for actual channel outputs, retaining the exact
zero reverse error. Equality of multiplicities and normalization force `Z=1`;
neither a reverse-error nor eigenvalue-ratio identity is assumed. -/
theorem theorem2_rank_one_of_block_realization (s : Finset ι)
    (depth m n : ι → ℕ) (pμ pν : ι → ℝ) (d D g : ℕ) (b a Z : ℝ)
    (R : BlockRealization s m n pμ pν
      (fun i => min 1 (2 * (depth i : ℝ) * (D : ℝ) / ((g : ℝ) + 2))) a H K)
    (hpμ : ∀ i ∈ s, 0 ≤ pμ i) (hpν : ∀ i ∈ s, 0 ≤ pν i)
    (ha : 0 ≤ a) (ha1 : a ≤ 1)
    (hdepth : ∀ i ∈ s, depth i = 0) (hmn : ∀ i ∈ s, m i = n i)
    (hratio : ∀ i ∈ s, pν i = Z * pμ i)
    (hdim : 1 - a ≤ (d.choose 2 : ℝ) * (D : ℝ) / (b + 1)) :
    traceDistance (R.forward.toFun (mixture s pμ R.Pμ)) (mixture s pν R.Pν) ≤
        Theorem2.cloningConstant d 1 0 * (D : ℝ) / (b + 1) ∧
    traceDistance (R.reverse.toFun (mixture s pν R.Pν)) (mixture s pμ R.Pμ) = 0 := by
  have hμ_norm : ∑ i ∈ s, pμ i * (m i : ℝ) = 1 := by
    have ht : tr (mixture s pμ R.Pμ) = 1 := by simp [tr, R.normalized_μ]
    rw [mixture_trace] at ht
    convert ht using 1
    apply Finset.sum_congr rfl
    intro i hi
    rw [R.trace_μ i hi]
  have hν_norm : ∑ i ∈ s, pν i * (m i : ℝ) = 1 := by
    have ht : tr (mixture s pν R.Pν) = 1 := by simp [tr, R.normalized_ν]
    rw [mixture_trace] at ht
    convert ht using 1
    apply Finset.sum_congr rfl
    intro i hi
    rw [R.trace_ν i hi, hmn i hi]
  have hZ : Z = 1 := by
    calc
      Z = Z * (∑ i ∈ s, pμ i * (m i : ℝ)) := by rw [hμ_norm, mul_one]
      _ = ∑ i ∈ s, pν i * (m i : ℝ) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i hi
        rw [hratio i hi, mul_assoc]
      _ = 1 := hν_norm
  obtain ⟨hf, hr⟩ := R.error_comparisons hpμ hpν
    (fun i _ => le_min (by norm_num) (by positivity)) ha ha1
    (by rw [hZ]; norm_num) (by rw [hZ]) hratio
  apply Theorem2.theorem2_rank_one s depth m n pμ pν d D g b _ _ a Z
    hdepth hZ (traceDistance_nonneg _ _) hdim hf hr

end FreeEntropy.CloningMatrices
