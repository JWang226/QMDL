/-
Copyright (c) 2026 Free Entropy formalization contributors.
See LICENSE and NOTICE in the repository root for license and attribution.
-/

import FreeEntropy.TraceMetric
import FreeEntropy.QuantumProtocol
import FreeEntropy.GeometricOrbit

/-!
# Haar-average transfer of actual quantum codes

A source code is transferred with encoder `E ∘ B` and decoder `A ∘ D`.
The integral error estimate follows from the proved matrix trace-distance
triangle and contraction laws. Compactness and continuity discharge all
integrability conditions. The final converse assumes only the original
source code error and quantitative source/target approximation bounds.
-/

noncomputable section
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.Elementwise Topology
open Matrix MeasureTheory MeasureTheory.Measure Filter
open FreeEntropy.OrbitMemory FreeEntropy.TraceDistance FreeEntropy.Channels
open FreeEntropy.GeometricOrbit FreeEntropy.Twirling

namespace FreeEntropy.QuantumTransfer
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 600000

variable {S T M X : Type*} [Fintype S] [DecidableEq S]
  [Fintype T] [DecidableEq T] [Fintype M] [DecidableEq M]

theorem channel_continuous (C : MatrixChannel S T) : Continuous C.toFun :=
  C.toRealLinearMap.continuous_of_finiteDimensional

variable [TopologicalSpace X] [CompactSpace X] [MeasurableSpace X]
  [OpensMeasurableSpace X]

theorem integrable_traceDistance (μ : Measure X) [IsFiniteMeasure μ]
    {ρ τ : X → Matrix T T ℂ} (hρ : Continuous ρ) (hτ : Continuous τ) :
    Integrable (fun x => traceDistance (ρ x) (τ x)) μ :=
  (continuous_traceDistance.comp (hρ.prodMk hτ)).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

/-- Exact integrated transfer inequality for continuous matrix families on
any compact probability space, in particular normalized Haar measure. -/
theorem compact_transferred_average_error
    (μ : Measure X) [IsProbabilityMeasure μ]
    (A : MatrixChannel S T) (B : MatrixChannel T S)
    (E : MatrixChannel S M) (D : MatrixChannel M S)
    (ρ : X → Matrix S S ℂ) (τ : X → Matrix T T ℂ)
    (hρc : Continuous ρ) (hτc : Continuous τ)
    (hρ : ∀ x, (ρ x).PosSemidef) (hτ : ∀ x, (τ x).PosSemidef) :
    (∫ x, traceDistance ((A.comp D).toFun ((E.comp B).toFun (τ x))) (τ x) ∂μ) ≤
      (∫ x, traceDistance (B.toFun (τ x)) (ρ x) ∂μ) +
      (∫ x, traceDistance (D.toFun (E.toFun (ρ x))) (ρ x) ∂μ) +
      (∫ x, traceDistance (A.toFun (ρ x)) (τ x) ∂μ) := by
  have hB := (channel_continuous B).comp hτc
  have hED := (channel_continuous D).comp ((channel_continuous E).comp hρc)
  have hA := (channel_continuous A).comp hρc
  have htrans := (channel_continuous (A.comp D)).comp
    ((channel_continuous (E.comp B)).comp hτc)
  have hr := integrable_traceDistance μ hB hρc
  have hc := integrable_traceDistance μ hED hρc
  have hf := integrable_traceDistance μ hA hτc
  have ht := integral_mono (integrable_traceDistance μ htrans hτc) ((hr.add hc).add hf)
    (fun x => QuantumProtocol.transferred_code_error A B E D (hρ x) (hτ x))
  simp only [Pi.add_apply, Function.comp_apply] at hr hc hf ht
  have hrc : Integrable (fun x => traceDistance (B.toFun (τ x)) (ρ x) +
      traceDistance (D.toFun (E.toFun (ρ x))) (ρ x)) μ := hr.add hc
  rw [integral_add hrc hf, integral_add hr hc] at ht
  exact ht

/-- Pointwise forward/reverse approximation bounds and the original source
code's average error bound give the transferred average error automatically. -/
theorem compact_transferred_average_error_le
    (μ : Measure X) [IsProbabilityMeasure μ]
    (A : MatrixChannel S T) (B : MatrixChannel T S)
    (E : MatrixChannel S M) (D : MatrixChannel M S)
    (ρ : X → Matrix S S ℂ) (τ : X → Matrix T T ℂ)
    (hρc : Continuous ρ) (hτc : Continuous τ)
    (hρ : ∀ x, (ρ x).PosSemidef) (hτ : ∀ x, (τ x).PosSemidef)
    (δ forwardError reverseError : ℝ)
    (hc : (∫ x, traceDistance (D.toFun (E.toFun (ρ x))) (ρ x) ∂μ) ≤ δ)
    (hf : ∀ x, traceDistance (A.toFun (ρ x)) (τ x) ≤ forwardError)
    (hr : ∀ x, traceDistance (B.toFun (τ x)) (ρ x) ≤ reverseError) :
    (∫ x, traceDistance ((A.comp D).toFun ((E.comp B).toFun (τ x))) (τ x) ∂μ) ≤
      δ + forwardError + reverseError := by
  have h := compact_transferred_average_error μ A B E D ρ τ hρc hτc hρ hτ
  have hf' := integral_mono
    (integrable_traceDistance μ ((channel_continuous A).comp hρc) hτc)
    (integrable_const forwardError) hf
  have hr' := integral_mono
    (integrable_traceDistance μ ((channel_continuous B).comp hτc) hρc)
    (integrable_const reverseError) hr
  simp only [Function.comp_apply, integral_const, probReal_univ, one_smul] at hf' hr'
  linarith

/-- An original source code together with channels comparing it to a
concrete irreducible weight orbit. Source and target dimensions may differ. -/
structure TransferCode (N : ℕ) (q : ℝ) (G : Type*) [Group G] [TopologicalSpace G]
    (source target memory : ℕ) where
  sourceState : G → Matrix (Fin source) (Fin source) ℂ
  continuous_source : Continuous sourceState
  source_positive : ∀ g, (sourceState g).PosSemidef
  source_trace : ∀ g, (sourceState g).trace = 1
  weights : WeightData (Fin target) N q
  U : G →* Matrix (Fin target) (Fin target) ℂ
  continuous_U : Continuous U
  unitary : ∀ g, (U g)ᴴ * U g = 1
  irreducible : Representation.IsIrreducible (matrixRepresentation U)
  forward : MatrixChannel (Fin source) (Fin target)
  reverse : MatrixChannel (Fin target) (Fin source)
  encoder : MatrixChannel (Fin source) (Fin memory)
  decoder : MatrixChannel (Fin memory) (Fin source)

variable {N source target memory : ℕ} {q : ℝ}
variable {G : Type*} [Group G] [TopologicalSpace G]

/-- The actual channels used in the orbit converse. -/
def TransferCode.transferred (C : TransferCode N q G source target memory) :
    GeometricOrbit.Code N q G target memory where
  weights := C.weights
  U := C.U
  continuous_U := C.continuous_U
  unitary := C.unitary
  irreducible := C.irreducible
  encoder := C.encoder.comp C.reverse
  decoder := C.forward.comp C.decoder

def TransferCode.targetState (C : TransferCode N q G source target memory) (g : G) :
    Matrix (Fin target) (Fin target) ℂ := C.U g * C.weights.state * (C.U g)ᴴ

def TransferCode.forwardError (C : TransferCode N q G source target memory) (g : G) : ℝ :=
  traceDistance (C.forward.toFun (C.sourceState g)) (C.targetState g)

def TransferCode.reverseError (C : TransferCode N q G source target memory) (g : G) : ℝ :=
  traceDistance (C.reverse.toFun (C.targetState g)) (C.sourceState g)

variable [IsTopologicalGroup G] [CompactSpace G] [MeasurableSpace G] [BorelSpace G]

def TransferCode.sourceAverageError (C : TransferCode N q G source target memory)
    (μ : Measure G) : ℝ :=
  ∫ g, traceDistance (C.decoder.toFun (C.encoder.toFun (C.sourceState g))) (C.sourceState g) ∂μ

theorem TransferCode.target_continuous (C : TransferCode N q G source target memory) :
    Continuous C.targetState := by
  have h : Continuous (fun g => conjugate C.U g C.weights.state) :=
    (C.continuous_U.mul continuous_const).mul (C.continuous_U.comp continuous_inv)
  simpa only [conjugate_eq_unitary_conjugate C.U C.unitary, TransferCode.targetState] using h

theorem TransferCode.target_positive (C : TransferCode N q G source target memory) (g : G) :
    (C.targetState g).PosSemidef := C.weights.state_positive.mul_mul_conjTranspose_same (C.U g)

/-- The transferred orbit code has the source error plus the two actual
approximation errors. This is proved for every compact probability measure. -/
theorem TransferCode.averageError_le (C : TransferCode N q G source target memory)
    (μ : Measure G) [IsProbabilityMeasure μ] (δ fwd rev : ℝ)
    (hsource : C.sourceAverageError μ ≤ δ)
    (hfwd : ∀ g, C.forwardError g ≤ fwd) (hrev : ∀ g, C.reverseError g ≤ rev) :
    C.transferred.averageError μ ≤ δ + fwd + rev := by
  exact compact_transferred_average_error_le μ C.forward C.reverse C.encoder C.decoder
    C.sourceState C.targetState C.continuous_source C.target_continuous
    C.source_positive C.target_positive δ fwd rev hsource hfwd hrev

/-- The transfer estimate also works when the two approximation errors are
controlled only on average. Compact continuity proves all needed integrability. -/
theorem TransferCode.averageError_le_of_average (C : TransferCode N q G source target memory)
    (μ : Measure G) [IsProbabilityMeasure μ] (δ fwd rev : ℝ)
    (hsource : C.sourceAverageError μ ≤ δ)
    (hfwd : (∫ g, C.forwardError g ∂μ) ≤ fwd)
    (hrev : (∫ g, C.reverseError g ∂μ) ≤ rev) :
    C.transferred.averageError μ ≤ δ + fwd + rev := by
  have ht := compact_transferred_average_error μ C.forward C.reverse C.encoder C.decoder
    C.sourceState C.targetState C.continuous_source C.target_continuous
    C.source_positive C.target_positive
  change C.transferred.averageError μ ≤
    (∫ g, C.reverseError g ∂μ) + C.sourceAverageError μ + (∫ g, C.forwardError g ∂μ) at ht
  linarith

/-- The finite memory converse after deriving, rather than assuming, the
error of the transferred source code. -/
theorem TransferCode.memory_bound (C : TransferCode N q G source target memory)
    (μ : Measure G) [IsMulLeftInvariant μ] [IsProbabilityMeasure μ]
    (hN : 0 < N) (hq : 0 ≤ q) (hq1 : q < 1) (δ fwd rev : ℝ)
    (hsource : C.sourceAverageError μ ≤ δ)
    (hfwd : ∀ g, C.forwardError g ≤ fwd) (hrev : ∀ g, C.reverseError g ≤ rev) :
    (target : ℝ) * (1 - (δ + fwd + rev) / (1 - q) ^ (N + 1)) ≤ (memory : ℝ) := by
  have hgap : 0 < (1 - q) ^ (N + 1) := pow_pos (by linarith) _
  have he := C.averageError_le μ δ fwd rev hsource hfwd hrev
  have hb := C.transferred.memory_bound μ hN hq hq1
  have hd := div_le_div_of_nonneg_right he hgap.le
  have hc : 1 - (δ + fwd + rev) / (1 - q) ^ (N + 1) ≤
      1 - C.transferred.averageError μ / (1 - q) ^ (N + 1) := by linarith
  exact (mul_le_mul_of_nonneg_left hc (Nat.cast_nonneg target)).trans hb

/-- Theorem 1 converse for original source codes transported by actual
channels. The only error estimates assumed are source-code accuracy and
forward/reverse approximation, such as the proved cloning bounds. -/
theorem theorem1_converse_of_transferred_weight_codes {d r : ℕ} (s : FixedSpectrum d r)
    (N : ℕ) (q : ℝ) (hN : 0 < N) (hq : 0 ≤ q) (hq1 : q < 1)
    (source memory target : ℕ → ℕ) (δ fwd rev : ℕ → ℝ)
    (μ : Measure G) [IsMulLeftInvariant μ] [IsProbabilityMeasure μ]
    (C : ∀ n, TransferCode N q G (source n) (target n) (memory n))
    (hdim : ∀ᶠ n in atTop, (target n : ℝ) = Weyl.activeProduct d r (s.targetRow n))
    (hδ : Tendsto δ atTop (𝓝 0))
    (hfscale : Asymptotics.IsBigO atTop fwd Weyl.errorScale)
    (hrscale : Asymptotics.IsBigO atTop rev Weyl.errorScale)
    (hsource : ∀ᶠ n in atTop, (C n).sourceAverageError μ ≤ δ n)
    (hfwd : ∀ᶠ n in atTop, ∀ g, (C n).forwardError g ≤ fwd n)
    (hrev : ∀ᶠ n in atTop, ∀ g, (C n).reverseError g ≤ rev n) :
    (0 : EReal) ≤ liminf
      (fun n => ((Real.logb 2 (memory n) - Weyl.qmdl d r s.eigenvalue n : ℝ) : EReal)) atTop := by
  apply GeometricOrbit.theorem1_converse_of_weight_codes s N q hN hq hq1
    memory target δ (fun n => fwd n + rev n) μ (fun n => (C n).transferred)
    hdim (fun n => Nat.zero_lt_of_lt (C n).weights.highest.isLt) hδ (hfscale.add hrscale)
  filter_upwards [hsource, hfwd, hrev] with n hn hf hr
  have he := (C n).averageError_le μ (δ n) (fwd n) (rev n) hn hf hr
  simpa only [add_assoc] using he

end FreeEntropy.QuantumTransfer
