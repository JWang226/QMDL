/-
Copyright (c) 2026 Free Entropy formalization contributors.
See LICENSE and NOTICE in the repository root for license and attribution.
-/

import FreeEntropy.SchurProtocol
import FreeEntropy.TypicalRows
import FreeEntropy.FiniteConcentration

/-!
# Achievability for the constructed Schur-sector code

The code below has concrete finite sector and multiplicity registers,
sector CPTP channels, density matrices, and a probability distribution.
Its encoder discards the multiplicity registers and its decoder restores
them. Its error is the actual trace distance of their roundtrip on the
explicit Schur block mixture. Local cloning bounds and an atypical tail
bound imply the full error rate; no bound on the full error is assumed.

Identifying the explicit block mixture with the tensor-power source, and
the memory dimension with the Weyl product, remains representation input.
-/

noncomputable section
open Filter
open scoped BigOperators Topology ComplexOrder MatrixOrder

namespace FreeEntropy.SchurAchievability

open Matrix Channels TraceDistance

/-- Finite quantum data of a Schur-sector code with a common memory register. -/
structure Code (memory : ℕ) where
  sectorCount : ℕ
  sectorDim : Fin sectorCount → ℕ
  multiplicityDim : Fin sectorCount → ℕ
  multiplicityPositive : ∀ i, 0 < multiplicityDim i
  probability : Fin sectorCount → ℝ
  probability_nonneg : ∀ i, 0 ≤ probability i
  probability_sum : ∑ i, probability i = 1
  state : ∀ i, Matrix (Fin (sectorDim i)) (Fin (sectorDim i)) ℂ
  state_positive : ∀ i, (state i).PosSemidef
  state_trace : ∀ i, (state i).trace = 1
  target : Matrix (Fin memory) (Fin memory) ℂ
  target_positive : target.PosSemidef
  target_trace : target.trace = 1
  forward : ∀ i, MatrixChannel (Fin (sectorDim i)) (Fin memory)
  reverse : ∀ i, MatrixChannel (Fin memory) (Fin (sectorDim i))
  row : Fin sectorCount → ℕ → ℤ
  typical : Finset (Fin sectorCount)

instance {m : ℕ} (C : Code m) (i : Fin C.sectorCount) :
    Nonempty (Fin (C.multiplicityDim i)) := Fin.pos_iff_nonempty.mp (C.multiplicityPositive i)

/-- The actual source space includes both irreducible and multiplicity registers. -/
abbrev Code.Source {m : ℕ} (C : Code m) :=
  (i : Fin C.sectorCount) × (Fin (C.sectorDim i) × Fin (C.multiplicityDim i))

def Code.source {m : ℕ} (C : Code m) : Matrix C.Source C.Source ℂ :=
  SchurProtocol.sourceState (A := fun i => Fin (C.multiplicityDim i)) C.probability C.state

def Code.encoder {m : ℕ} (C : Code m) : MatrixChannel C.Source (Fin m) :=
  SchurProtocol.encoder (A := fun i => Fin (C.multiplicityDim i)) C.forward

def Code.decoder {m : ℕ} (C : Code m) : MatrixChannel (Fin m) C.Source :=
  SchurProtocol.decoder (A := fun i => Fin (C.multiplicityDim i))
    C.reverse C.probability C.probability_nonneg C.probability_sum

theorem Code.source_positive {m : ℕ} (C : Code m) : C.source.PosSemidef :=
  SchurProtocol.sourceState_positive C.probability C.probability_nonneg C.state C.state_positive

theorem Code.source_trace {m : ℕ} (C : Code m) : C.source.trace = 1 :=
  SchurProtocol.sourceState_trace C.probability C.probability_sum C.state C.state_trace

/-- The error of the constructed encoder/decoder on the actual Schur block mixture. -/
def Code.error {m : ℕ} (C : Code m) : ℝ :=
  traceDistance (C.decoder.toFun (C.encoder.toFun C.source)) C.source

theorem Code.error_nonneg {m : ℕ} (C : Code m) : 0 ≤ C.error :=
  traceDistance_nonneg _ _

def Code.tail {m : ℕ} (C : Code m) : ℝ :=
  Protocol.outsideMass Finset.univ C.typical C.probability

/-- The whole-code trace error is derived from its sector errors. -/
theorem Code.error_le_sector_errors {m : ℕ} (C : Code m) (ε : ℝ) (hε : 0 ≤ ε)
    (hf : ∀ i ∈ C.typical, traceDistance ((C.forward i).toFun (C.state i)) C.target ≤ ε)
    (hr : ∀ i ∈ C.typical, traceDistance ((C.reverse i).toFun C.target) (C.state i) ≤ ε) :
    C.error ≤ 2 * ε + 2 * C.tail :=
  SchurProtocol.typical_roundtrip_error C.forward C.reverse C.probability
    C.probability_nonneg C.probability_sum C.state C.state_positive C.state_trace
    C.target C.target_positive C.target_trace C.typical ε hε hf hr

/-- A fixed coefficient for the uniform typical-row cloning rate. -/
def rateConstant {d r : ℕ} (s : FixedSpectrum d r) (hd : 2 ≤ d) (K : ℝ) : ℝ :=
  2 * K * ((r : ℝ) * (3 * r + 2)) / TypicalRows.minimumGap s hd

theorem rateConstant_nonneg {d r : ℕ} (s : FixedSpectrum d r)
    (hd : 2 ≤ d) (K : ℝ) (hK : 0 ≤ K) : 0 ≤ rateConstant s hd K := by
  have hg := TypicalRows.minimumGap_pos s hd
  unfold rateConstant
  positivity

theorem errorScale_nonneg (n : ℕ) (hn : 2 ≤ n) : 0 ≤ Weyl.errorScale n := by
  unfold Weyl.errorScale
  exact div_nonneg (Real.logb_nonneg (by norm_num) (by exact_mod_cast (show 1 ≤ n by omega)))
    (Real.sqrt_nonneg _)

/-- The actual finite cloning envelope used for each typical sector. -/
def cloningEnvelope {d r : ℕ} (s : FixedSpectrum d r) (hd : 2 ≤ d)
    (K : ℝ) (n : ℕ) (μ : ℕ → ℤ) : ℝ :=
  K * Weyl.rowL1 d (fun i => s.targetRow n i - (μ i : ℝ)) /
    ((n : ℝ) * TypicalRows.minimumGap s hd / 2 + 1)

/-- The whole-code error bound follows uniformly from the finite per-row
cloning estimates and the actual typical-window predicate. -/
theorem Code.error_le_from_rows {d r m : ℕ} (C : Code m)
    (s : FixedSpectrum d r) (hd : 2 ≤ d) (K : ℝ) (hK : 0 ≤ K)
    (n : ℕ) (hn : 2 ≤ n)
    (htyp : ∀ i ∈ C.typical, TypicalRows.Typical s n (C.row i))
    (hf : ∀ i ∈ C.typical, traceDistance ((C.forward i).toFun (C.state i)) C.target ≤
      cloningEnvelope s hd K n (C.row i))
    (hr : ∀ i ∈ C.typical, traceDistance ((C.reverse i).toFun C.target) (C.state i) ≤
      cloningEnvelope s hd K n (C.row i)) :
    C.error ≤ 2 * (rateConstant s hd K * Weyl.errorScale n) + 2 * C.tail := by
  apply C.error_le_sector_errors _
    (mul_nonneg (rateConstant_nonneg s hd K hK) (errorScale_nonneg n hn))
  · intro i hi
    exact (hf i hi).trans (TypicalRows.cloning_envelope_le s hd K hK n hn (C.row i) (htyp i hi))
  · intro i hi
    exact (hr i hi).trans (TypicalRows.cloning_envelope_le s hd K hK n hn (C.row i) (htyp i hi))

/-- Theorem 1 achievability for an actual sequence of constructed quantum
codes. The local sector estimates and atypical probability imply the total
trace-distance error rate. The tail input `≤1/n` is sufficient, including
when obtained from a weaker proved relative-entropy bound than Pinsker's
optimal constant.
-/
theorem theorem1_schur_achievability {d r : ℕ} (s : FixedSpectrum d r) (hd : 2 ≤ d)
    (memory : ℕ → ℕ) (code : ∀ n, Code (memory n)) (K : ℝ) (hK : 0 ≤ K)
    (hdim : ∀ᶠ n in atTop, (memory n : ℝ) = Weyl.activeProduct d r (s.targetRow n))
    (htyp : ∀ᶠ n in atTop, ∀ i ∈ (code n).typical,
      TypicalRows.Typical s n ((code n).row i))
    (hf : ∀ᶠ n in atTop, ∀ i ∈ (code n).typical,
      traceDistance (((code n).forward i).toFun ((code n).state i)) (code n).target ≤
        cloningEnvelope s hd K n ((code n).row i))
    (hr : ∀ᶠ n in atTop, ∀ i ∈ (code n).typical,
      traceDistance (((code n).reverse i).toFun (code n).target) ((code n).state i) ≤
        cloningEnvelope s hd K n ((code n).row i))
    (htail : ∀ᶠ n in atTop, (code n).tail ≤ 1 / (n : ℝ)) :
    Tendsto (fun n => Real.logb 2 (memory n) - Weyl.qmdl d r s.eigenvalue n) atTop (𝓝 0) ∧
      Asymptotics.IsBigO atTop (fun n => (code n).error) Weyl.errorScale ∧
      Tendsto (fun n => (code n).error) atTop (𝓝 0) := by
  have hfinite : ∀ᶠ n in atTop,
      (code n).error ≤ 2 * (rateConstant s hd K * Weyl.errorScale n) + 2 * (1 / (n : ℝ)) := by
    filter_upwards [htyp, hf, hr, htail, eventually_ge_atTop 2] with n hn hf hr ht hn2
    have he := (code n).error_le_from_rows s hd K hK n hn2 hn hf hr
    linarith
  have hrate : ∀ᶠ n in atTop, 0 ≤ Weyl.errorScale n := by
    filter_upwards [eventually_ge_atTop 2] with n hn
    exact errorScale_nonneg n hn
  have hinv : ∀ᶠ (n : ℕ) in atTop, 1 / (n : ℝ) ≤ 1 * Weyl.errorScale n := by
    filter_upwards [eventually_ge_atTop 2] with n hn
    simpa only [one_mul] using Concentration.inv_le_errorScale n hn
  have hbig : Asymptotics.IsBigO atTop (fun n => (code n).error) Weyl.errorScale :=
    Protocol.error_isBigO (C := rateConstant s hd K) (T := 1)
      (Eventually.of_forall fun n => (code n).error_nonneg) hrate hfinite
      (Eventually.of_forall fun _ => le_rfl) hinv
  refine ⟨?_, hbig, hbig.trans_tendsto Weyl.errorScale_tendsto_zero⟩
  have hm := Weyl.activeProduct_log_asymptotic d r s.targetRow s.eigenvalue
    s.active_gap s.targetRow_normalized_tendsto
  have hmem : Tendsto (fun n => Real.logb 2 (memory n) - Weyl.rootLeading d r s.eigenvalue n)
      atTop (𝓝 0) := by
    apply hm.congr'
    filter_upwards [hdim] with n hn
    rw [hn]
  simpa only [Weyl.rootLeading_eq_qmdl d r s.rank_le s.eigenvalue _
    s.active_gap s.zero_padded] using hmem

/-- Concrete diagram data and the pointwise Schur probability estimate.
The total tail estimate is deliberately absent: it will be proved from
this local formula, normalization of the rows, and actual diagram counting. -/
structure Code.DiagramEstimate {d r m : ℕ} (s : FixedSpectrum d r)
    (n : ℕ) (C : Code m) : Prop where
  row_injective : Function.Injective (fun a (i : Fin r) => C.row a i)
  row_nonneg : ∀ a i, i < r → 0 ≤ C.row a i
  row_le_n : ∀ a i, i < r → C.row a i ≤ (n : ℤ)
  row_zero : ∀ a i, r ≤ i → i < d → C.row a i = 0
  row_size : ∀ a, ∑ i : Fin r, C.row a i = (n : ℤ)
  mem_typical : ∀ a, a ∈ C.typical ↔ TypicalRows.Typical s n (C.row a)
  pointwise : ∀ a, C.probability a ≤ ((n : ℝ) + 1) ^ (r.choose 2) * Real.exp
    (-(n : ℝ) * FiniteConcentration.kl (FiniteConcentration.rowFrequency r n (C.row a))
      (fun i : Fin r => s.eigenvalue i))

/-- The actual atypical mass is derived from the explicit pointwise diagram estimate. -/
theorem Code.tail_le_from_diagrams {d r m : ℕ} (s : FixedSpectrum d r)
    (n : ℕ) (hn : 2 ≤ n) (C : Code m) (h : C.DiagramEstimate s n) :
    C.tail ≤ Concentration.tailBound (r.choose 2 + r) n := by
  classical
  have ht : C.tail = ∑ a ∈ Finset.univ.filter (fun a => ¬ TypicalRows.Typical s n (C.row a)),
      C.probability a := by
    unfold Code.tail Protocol.outsideMass
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro a _
    by_cases ha : a ∈ C.typical
    · simp [ha, (h.mem_typical a).mp ha]
    · have hnot : ¬ TypicalRows.Typical s n (C.row a) := fun ht => ha ((h.mem_typical a).mpr ht)
      simp [ha, hnot]
  rw [ht]
  exact FiniteConcentration.schur_atypical_tail_le s n hn C.row C.probability
    h.row_injective h.row_nonneg h.row_le_n h.row_zero h.row_size h.pointwise

/-- Theorem 1 for the constructed Schur protocol with its probability tail
derived from pointwise diagram probabilities. Only the local sector cloning
estimate, the pointwise representation probability estimate, and the Weyl
dimension identity remain; no aggregate-error or aggregate-tail bound is assumed. -/
theorem theorem1_schur_achievability_of_pointwise {d r : ℕ}
    (s : FixedSpectrum d r) (hd : 2 ≤ d)
    (memory : ℕ → ℕ) (code : ∀ n, Code (memory n)) (K : ℝ) (hK : 0 ≤ K)
    (hdim : ∀ᶠ n in atTop, (memory n : ℝ) = Weyl.activeProduct d r (s.targetRow n))
    (hdiagrams : ∀ᶠ n in atTop, (code n).DiagramEstimate s n)
    (hf : ∀ᶠ n in atTop, ∀ i ∈ (code n).typical,
      traceDistance (((code n).forward i).toFun ((code n).state i)) (code n).target ≤
        cloningEnvelope s hd K n ((code n).row i))
    (hr : ∀ᶠ n in atTop, ∀ i ∈ (code n).typical,
      traceDistance (((code n).reverse i).toFun (code n).target) ((code n).state i) ≤
        cloningEnvelope s hd K n ((code n).row i)) :
    Tendsto (fun n => Real.logb 2 (memory n) - Weyl.qmdl d r s.eigenvalue n) atTop (𝓝 0) ∧
      Asymptotics.IsBigO atTop (fun n => (code n).error) Weyl.errorScale ∧
      Tendsto (fun n => (code n).error) atTop (𝓝 0) := by
  apply theorem1_schur_achievability s hd memory code K hK hdim ?_ hf hr ?_
  · filter_upwards [hdiagrams] with n hn
    exact fun i hi => (hn.mem_typical i).mp hi
  · filter_upwards [hdiagrams, Concentration.tailBound_eventually_le_inv (r.choose 2 + r),
      eventually_ge_atTop 2] with n hn ht hn2
    exact ((code n).tail_le_from_diagrams s n hn2 hn).trans ht

end FreeEntropy.SchurAchievability
