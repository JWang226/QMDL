/-
Copyright (c) 2026 Free Entropy formalization contributors.
See LICENSE and NOTICE in the repository root for license and attribution.
-/

import FreeEntropy.PhysicalCanonicalConverse

/-! Worst-case error of an actual physical tensor-source code. The error
is the supremum over U(d), and comparison bounds imply the uniform rate. -/
noncomputable section
open Matrix MeasureTheory Filter
open scoped Topology Matrix.Norms.Elementwise ComplexOrder MatrixOrder
namespace FreeEntropy.SchurWeyl
open Channels TraceDistance ExteriorRepresentation
set_option backward.isDefEq.respectTransparency false
variable {d r : ℕ} {B : Type*} [Fintype B] [DecidableEq B]

theorem physicalSource_trace (s : FixedSpectrum d r) (n : ℕ)
    (U : Matrix.unitaryGroup (Fin d) ℂ) : (physicalSource s n U).trace = 1 := by
  rw [physicalSource, TensorPowers.matrix_trace, physicalDensity_trace, one_pow]

def mixedWorstError (s : FixedSpectrum d r) (n : ℕ)
    (E : MatrixChannel (Fin n → Fin d) B) (D : MatrixChannel B (Fin n → Fin d)) : ℝ :=
  sSup (Set.range (fun U : Matrix.unitaryGroup (Fin d) ℂ =>
    traceDistance (D.toFun (E.toFun (physicalSource s n U))) (physicalSource s n U)))

theorem physical_error_le_one (s : FixedSpectrum d r) (n : ℕ)
    (E : MatrixChannel (Fin n → Fin d) B) (D : MatrixChannel B (Fin n → Fin d))
    (U : Matrix.unitaryGroup (Fin d) ℂ) :
    traceDistance (D.toFun (E.toFun (physicalSource s n U))) (physicalSource s n U) ≤ 1 :=
  traceDistance_states_le_one (D.positive _ (E.positive _ (physicalSource_positive s n U)))
    (physicalSource_positive s n U)
    (by rw [D.trace_preserving, E.trace_preserving, physicalSource_trace]) (physicalSource_trace s n U)

theorem physical_error_le_worst (s : FixedSpectrum d r) (n : ℕ)
    (E : MatrixChannel (Fin n → Fin d) B) (D : MatrixChannel B (Fin n → Fin d))
    (U : Matrix.unitaryGroup (Fin d) ℂ) :
    traceDistance (D.toFun (E.toFun (physicalSource s n U))) (physicalSource s n U) ≤
      mixedWorstError s n E D := by
  apply le_csSup _ (Set.mem_range_self U)
  exact ⟨1, by rintro _ ⟨V, rfl⟩; exact physical_error_le_one s n E D V⟩

theorem mixedWorstError_nonneg (s : FixedSpectrum d r) (n : ℕ)
    (E : MatrixChannel (Fin n → Fin d) B) (D : MatrixChannel B (Fin n → Fin d)) :
    0 ≤ mixedWorstError s n E D :=
  (traceDistance_nonneg _ _).trans (physical_error_le_worst s n E D 1)

theorem mixedWorstError_le (s : FixedSpectrum d r) (n : ℕ)
    (E : MatrixChannel (Fin n → Fin d) B) (D : MatrixChannel B (Fin n → Fin d))
    (bound : ℝ)
    (hbound : ∀ U, traceDistance (D.toFun (E.toFun (physicalSource s n U)))
      (physicalSource s n U) ≤ bound) : mixedWorstError s n E D ≤ bound := by
  apply csSup_le (Set.range_nonempty _) _
  rintro _ ⟨U, rfl⟩
  exact hbound U

theorem mixedAverageError_nonneg (s : FixedSpectrum d r) (n : ℕ)
    (E : MatrixChannel (Fin n → Fin d) B) (D : MatrixChannel B (Fin n → Fin d)) :
    0 ≤ mixedAverageError s n E D := integral_nonneg (fun _ => traceDistance_nonneg _ _)

theorem mixedAverageError_le_worst (s : FixedSpectrum d r) (n : ℕ)
    (E : MatrixChannel (Fin n → Fin d) B) (D : MatrixChannel B (Fin n → Fin d)) :
    mixedAverageError s n E D ≤ mixedWorstError s n E D := by
  have hc := physicalSource_continuous s n
  have hi := QuantumTransfer.integrable_traceDistance (UnitaryHaar.probabilityHaar (Fin d))
    ((QuantumTransfer.channel_continuous D).comp ((QuantumTransfer.channel_continuous E).comp hc)) hc
  have h := integral_mono hi (integrable_const (mixedWorstError s n E D))
    (physical_error_le_worst s n E D)
  simpa only [mixedAverageError, integral_const, probReal_univ, one_smul] using h

theorem mixedAverageError_tendsto_of_uniform (s : FixedSpectrum d r) (memory : ℕ → ℕ)
    (E : ∀ n, MatrixChannel (Fin n → Fin d) (Fin (memory n)))
    (D : ∀ n, MatrixChannel (Fin (memory n)) (Fin n → Fin d))
    (h : Tendsto (fun n => mixedWorstError s n (E n) (D n)) atTop (𝓝 0)) :
    Tendsto (fun n => mixedAverageError s n (E n) (D n)) atTop (𝓝 0) :=
  squeeze_zero (fun n => mixedAverageError_nonneg s n (E n) (D n))
    (fun n => mixedAverageError_le_worst s n (E n) (D n)) h

theorem physical_roundtrip_of_comparison (s : FixedSpectrum d r) (hd : 2 ≤ d) (n : ℕ)
    (A : MatrixChannel (Fin n → Fin d) (IrrepIndex (targetCanonicalRow s n)))
    (R : MatrixChannel (IrrepIndex (targetCanonicalRow s n)) (Fin n → Fin d))
    (f g : ℝ)
    (hf : ∀ U, traceDistance (A.toFun (physicalSource s n U))
      (canonicalOrbitState s (targetCanonicalRow s n) U) ≤ f)
    (hr : ∀ U, traceDistance (R.toFun (canonicalOrbitState s (targetCanonicalRow s n) U))
      (physicalSource s n U) ≤ g) : mixedWorstError s n A R ≤ f + g := by
  apply mixedWorstError_le
  intro U
  exact (QuantumProtocol.roundtrip_error A R (physicalSource_positive s n U)
    (canonicalOrbitState_positive s (targetCanonicalRow s n) hd U)).trans (add_le_add (hf U) (hr U))

/-- Achievability for the literal source in worst-case trace distance,
using the actual canonical memory dimension and actual comparison channels. -/
theorem theorem1_physical_achievability_of_comparison (s : FixedSpectrum d r) (hd : 2 ≤ d)
    (A : ∀ n, MatrixChannel (Fin n → Fin d) (IrrepIndex (targetCanonicalRow s n)))
    (R : ∀ n, MatrixChannel (IrrepIndex (targetCanonicalRow s n)) (Fin n → Fin d))
    (f g : ℕ → ℝ)
    (hf : ∀ᶠ n in atTop, ∀ U, traceDistance ((A n).toFun (physicalSource s n U))
      (canonicalOrbitState s (targetCanonicalRow s n) U) ≤ f n)
    (hr : ∀ᶠ n in atTop, ∀ U, traceDistance ((R n).toFun (canonicalOrbitState s (targetCanonicalRow s n) U))
      (physicalSource s n U) ≤ g n)
    (hfg : Asymptotics.IsBigO atTop (fun n => f n + g n) Weyl.errorScale) :
    Tendsto (fun n => Real.logb 2 (targetCanonicalDimension s n) -
      Weyl.qmdl d r s.eigenvalue n) atTop (𝓝 0) ∧
      Asymptotics.IsBigO atTop (fun n => mixedWorstError s n (A n) (R n)) Weyl.errorScale ∧
      Tendsto (fun n => mixedWorstError s n (A n) (R n)) atTop (𝓝 0) := by
  have hle : ∀ᶠ n in atTop, mixedWorstError s n (A n) (R n) ≤ f n + g n := by
    filter_upwards [hf, hr] with n hfn hrn
    exact physical_roundtrip_of_comparison s hd n (A n) (R n) (f n) (g n) hfn hrn
  have hbig : Asymptotics.IsBigO atTop (fun n => mixedWorstError s n (A n) (R n))
      (fun n => f n + g n) := by
    apply Asymptotics.IsBigO.of_bound'
    filter_upwards [hle] with n hn
    rw [Real.norm_eq_abs, abs_of_nonneg (mixedWorstError_nonneg s n (A n) (R n)), Real.norm_eq_abs]
    exact hn.trans (le_abs_self _)
  have hrate := hbig.trans hfg
  exact ⟨targetCanonicalDimension_log_asymptotic s, hrate, hrate.trans_tendsto Weyl.errorScale_tendsto_zero⟩

end FreeEntropy.SchurWeyl
