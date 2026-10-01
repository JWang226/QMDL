/-
Copyright (c) 2026 Free Entropy formalization contributors.
See LICENSE and NOTICE in the repository root for license and attribution.
-/

import FreeEntropy.TraceDistance
import FreeEntropy.Twirling
import FreeEntropy.SpectrumBounds
import FreeEntropy.Channels
import Mathlib.MeasureTheory.Function.LocallyIntegrable

/-!
# The orbit memory bound with actual average trace-distance error

This removes the testing-error hypothesis of `OrbitMemory` using the proved
measurement inequality for `Tr sqrt(X†X)`. Representation-theoretic twirling
and spectral data remain explicit inputs; the error is now a genuine matrix
trace-distance integral.
-/

open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.Elementwise
open Matrix MeasureTheory
open FreeEntropy.OrbitMemory FreeEntropy.TraceDistance

namespace FreeEntropy.OrbitTraceDistance

set_option backward.isDefEq.respectTransparency false

variable {H M X : Type*} [Fintype H] [DecidableEq H]
  [Fintype M] [DecidableEq M] [MeasurableSpace X]

omit [DecidableEq M] in
/-- Pointwise orbit testing follows from actual matrix trace distance. -/
theorem orbit_test_lower
    (E : Matrix H H ℂ →ₗ[ℝ] Matrix M M ℂ)
    (D : Matrix M M ℂ →ₗ[ℝ] Matrix H H ℂ)
    (hE : ∀ A, A.PosSemidef → (E A).PosSemidef)
    (hD : ∀ A, A.PosSemidef → (D A).PosSemidef)
    (hEt : ∀ A, (E A).trace = A.trace)
    (hDt : ∀ A, (D A).trace = A.trace)
    {P τ : Matrix H H ℂ}
    (hP : P.PosSemidef) (hPt : P.trace = 1) (hτ : τ.PosSemidef)
    {p₀ : ℝ} (hpeak : tr (P * τ) = p₀) :
    p₀ - traceDistance (D (E τ)) τ ≤ tr (P * D (E τ)) := by
  have hstate := hD (E τ) (hE τ hτ)
  have ht : (D (E τ)).trace = τ.trace := by rw [hDt, hEt]
  have hb := state_measurement_bound hstate hτ ht hP (state_le_one hP hPt)
  rw [hpeak] at hb
  have hl := (abs_le.mp hb).1
  linarith

omit [DecidableEq M] in
/-- The missing average testing estimate is derived from the integral of
actual trace distance, not supplied as a hypothesis. -/
theorem integral_orbit_test_lower
    (μ : Measure X) [IsProbabilityMeasure μ]
    (E : Matrix H H ℂ →ₗ[ℝ] Matrix M M ℂ)
    (D : Matrix M M ℂ →ₗ[ℝ] Matrix H H ℂ)
    (hE : ∀ A, A.PosSemidef → (E A).PosSemidef)
    (hD : ∀ A, A.PosSemidef → (D A).PosSemidef)
    (hEt : ∀ A, (E A).trace = A.trace)
    (hDt : ∀ A, (D A).trace = A.trace)
    (P τ : X → Matrix H H ℂ)
    (hP : ∀ x, (P x).PosSemidef) (hPt : ∀ x, (P x).trace = 1)
    (hτ : ∀ x, (τ x).PosSemidef)
    {p₀ : ℝ} (hpeak : ∀ x, tr (P x * τ x) = p₀)
    (hi : Integrable (fun x => tr (P x * D (E (τ x)))) μ)
    (hδi : Integrable (fun x => traceDistance (D (E (τ x))) (τ x)) μ) :
    p₀ - (∫ x, traceDistance (D (E (τ x))) (τ x) ∂μ) ≤
      ∫ x, tr (P x * D (E (τ x))) ∂μ := by
  have hl := integral_mono ((integrable_const p₀).sub hδi) hi
    (fun x => orbit_test_lower E D hE hD hEt hDt (hP x) (hPt x) (hτ x) (hpeak x))
  simpa [integral_sub (integrable_const p₀) hδi] using hl

/-- The orbit memory lower bound with its actual trace-distance error.
The remaining hypotheses are spectral/twirling data and integrability. -/
theorem integral_orbit_memory_bound [Nonempty H]
    (μ : Measure X) [IsProbabilityMeasure μ]
    (E : Matrix H H ℂ →ₗ[ℝ] Matrix M M ℂ)
    (D : Matrix M M ℂ →ₗ[ℝ] Matrix H H ℂ)
    (hE : ∀ A, A.PosSemidef → (E A).PosSemidef)
    (hD : ∀ A, A.PosSemidef → (D A).PosSemidef)
    (hEt : ∀ A, (E A).trace = A.trace)
    (hDt : ∀ A, (D A).trace = A.trace)
    (P τ : X → Matrix H H ℂ)
    (hP : ∀ x, (P x).PosSemidef) (hPt : ∀ x, (P x).trace = 1)
    (hτ : ∀ x, (τ x).PosSemidef)
    (hPi : Integrable P μ)
    (htwirl : ∫ x, P x ∂μ = (Fintype.card H : ℝ)⁻¹ • (1 : Matrix H H ℂ))
    {p₀ p₁ γ : ℝ} (hγ : 0 < γ) (hgap : γ = p₀ - p₁)
    (hpeak : ∀ x, tr (P x * τ x) = p₀)
    (hspec : ∀ x, τ x ≤ p₁ • (1 : Matrix H H ℂ) + γ • P x)
    (hi : Integrable (fun x => tr (P x * D (E (τ x)))) μ)
    (hδi : Integrable (fun x => traceDistance (D (E (τ x))) (τ x)) μ) :
    (Fintype.card H : ℝ) *
      (1 - (∫ x, traceDistance (D (E (τ x))) (τ x) ∂μ) / γ) ≤ (Fintype.card M : ℝ) := by
  exact OrbitMemory.integral_orbit_memory_bound μ E D hE hD hEt hDt
    P τ hP hPt hPi htwirl hγ hgap hspec hi
    (integral_orbit_test_lower μ E D hE hD hEt hDt P τ hP hPt hτ hpeak hi hδi)

/-- A numerical upper bound on the average trace-distance error gives the
usual parameterized memory bound. -/
theorem integral_orbit_memory_bound_of_error_le [Nonempty H]
    (μ : Measure X) [IsProbabilityMeasure μ]
    (E : Matrix H H ℂ →ₗ[ℝ] Matrix M M ℂ)
    (D : Matrix M M ℂ →ₗ[ℝ] Matrix H H ℂ)
    (hE : ∀ A, A.PosSemidef → (E A).PosSemidef)
    (hD : ∀ A, A.PosSemidef → (D A).PosSemidef)
    (hEt : ∀ A, (E A).trace = A.trace)
    (hDt : ∀ A, (D A).trace = A.trace)
    (P τ : X → Matrix H H ℂ)
    (hP : ∀ x, (P x).PosSemidef) (hPt : ∀ x, (P x).trace = 1)
    (hτ : ∀ x, (τ x).PosSemidef)
    (hPi : Integrable P μ)
    (htwirl : ∫ x, P x ∂μ = (Fintype.card H : ℝ)⁻¹ • (1 : Matrix H H ℂ))
    {p₀ p₁ γ δ : ℝ} (hγ : 0 < γ) (hgap : γ = p₀ - p₁)
    (hpeak : ∀ x, tr (P x * τ x) = p₀)
    (hspec : ∀ x, τ x ≤ p₁ • (1 : Matrix H H ℂ) + γ • P x)
    (hi : Integrable (fun x => tr (P x * D (E (τ x)))) μ)
    (hδi : Integrable (fun x => traceDistance (D (E (τ x))) (τ x)) μ)
    (hδ : (∫ x, traceDistance (D (E (τ x))) (τ x) ∂μ) ≤ δ) :
    (Fintype.card H : ℝ) * (1 - δ / γ) ≤ (Fintype.card M : ℝ) := by
  apply OrbitMemory.integral_orbit_memory_bound μ E D hE hD hEt hDt
    P τ hP hPt hPi htwirl hγ hgap hspec hi
  have ht := integral_orbit_test_lower μ E D hE hD hEt hDt P τ hP hPt hτ hpeak hi hδi
  linarith

section Compact

variable [TopologicalSpace X] [CompactSpace X] [OpensMeasurableSpace X]

/-- For continuous orbits on a compact space, all integrability requirements
follow automatically. In particular this applies to continuous unitary
orbits of compact groups with normalized Haar measure. -/
theorem compact_orbit_memory_bound [Nonempty H]
    (μ : Measure X) [IsProbabilityMeasure μ]
    (E : Matrix H H ℂ →ₗ[ℝ] Matrix M M ℂ)
    (D : Matrix M M ℂ →ₗ[ℝ] Matrix H H ℂ)
    (hE : ∀ A, A.PosSemidef → (E A).PosSemidef)
    (hD : ∀ A, A.PosSemidef → (D A).PosSemidef)
    (hEt : ∀ A, (E A).trace = A.trace)
    (hDt : ∀ A, (D A).trace = A.trace)
    (P τ : X → Matrix H H ℂ)
    (hP : ∀ x, (P x).PosSemidef) (hPt : ∀ x, (P x).trace = 1)
    (hτ : ∀ x, (τ x).PosSemidef)
    (hPc : Continuous P) (hτc : Continuous τ)
    (htwirl : ∫ x, P x ∂μ = (Fintype.card H : ℝ)⁻¹ • (1 : Matrix H H ℂ))
    {p₀ p₁ γ : ℝ} (hγ : 0 < γ) (hgap : γ = p₀ - p₁)
    (hpeak : ∀ x, tr (P x * τ x) = p₀)
    (hspec : ∀ x, τ x ≤ p₁ • (1 : Matrix H H ℂ) + γ • P x) :
    (Fintype.card H : ℝ) *
      (1 - (∫ x, traceDistance (D (E (τ x))) (τ x) ∂μ) / γ) ≤ (Fintype.card M : ℝ) := by
  have hout : Continuous (fun x => D (E (τ x))) :=
    D.continuous_of_finiteDimensional.comp (E.continuous_of_finiteDimensional.comp hτc)
  have htr : Continuous (tr : Matrix H H ℂ → ℝ) :=
    (LinearMap.toContinuousLinearMap
      (Complex.reCLM.toLinearMap.comp (Matrix.traceLinearMap H ℝ ℂ))).continuous
  have hov : Continuous (fun x => tr (P x * D (E (τ x)))) := htr.comp (hPc.mul hout)
  have hdist : Continuous (fun x => traceDistance (D (E (τ x))) (τ x)) := by
    change Continuous (fun x => traceNorm (D (E (τ x)) - τ x) / 2)
    exact ((continuous_traceNorm (H := H)).comp (hout.sub hτc)).div_const 2
  exact integral_orbit_memory_bound μ E D hE hD hEt hDt P τ hP hPt hτ
    (hPc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
    htwirl hγ hgap hpeak hspec
    (hov.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
    (hdist.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))

end Compact

section CompactGroup

open MeasureTheory.Measure FreeEntropy.Twirling

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [MeasurableSpace G] [BorelSpace G]

/-- Concrete continuous irreducible unitary orbits satisfy the memory bound.
Twirling and all integrability and trace-distance testing facts are proved;
the hypotheses `hpeak` and `hspec` state the spectral data of the input. -/
theorem irreducible_orbit_memory_bound [Nonempty H]
    (μ : Measure G) [IsMulLeftInvariant μ] [IsProbabilityMeasure μ]
    (U : G →* Matrix H H ℂ) (hU : Continuous U)
    (hunitary : ∀ g, (U g)ᴴ * U g = 1)
    [Representation.IsIrreducible (matrixRepresentation U)]
    (E : Matrix H H ℂ →ₗ[ℝ] Matrix M M ℂ)
    (D : Matrix M M ℂ →ₗ[ℝ] Matrix H H ℂ)
    (hE : ∀ A, A.PosSemidef → (E A).PosSemidef)
    (hD : ∀ A, A.PosSemidef → (D A).PosSemidef)
    (hEt : ∀ A, (E A).trace = A.trace)
    (hDt : ∀ A, (D A).trace = A.trace)
    (P τ : Matrix H H ℂ) (hP : P.PosSemidef) (hPt : P.trace = 1) (hτ : τ.PosSemidef)
    {p₀ p₁ : ℝ} (hgap : 0 < p₀ - p₁)
    (hpeak : tr (P * τ) = p₀)
    (hspec : τ ≤ p₁ • (1 : Matrix H H ℂ) + (p₀ - p₁) • P) :
    (Fintype.card H : ℝ) * (1 -
      (∫ g, traceDistance (D (E (U g * τ * (U g)ᴴ))) (U g * τ * (U g)ᴴ) ∂μ) /
        (p₀ - p₁)) ≤ (Fintype.card M : ℝ) := by
  have horbitc (A : Matrix H H ℂ) : Continuous (fun g => U g * A * (U g)ᴴ) := by
    have h : Continuous (fun g => conjugate U g A) :=
      (hU.mul continuous_const).mul (hU.comp continuous_inv)
    simpa only [conjugate_eq_unitary_conjugate U hunitary] using h
  have htrace (A : Matrix H H ℂ) (g : G) : (U g * A * (U g)ᴴ).trace = A.trace := by
    rw [Matrix.trace_mul_cycle, hunitary, Matrix.one_mul]
  have hpair (g : G) : tr ((U g * P * (U g)ᴴ) * (U g * τ * (U g)ᴴ)) = p₀ := by
    have hid : (U g * P * (U g)ᴴ) * (U g * τ * (U g)ᴴ) = U g * (P * τ) * (U g)ᴴ := by
      calc
        _ = U g * P * ((U g)ᴴ * U g) * τ * (U g)ᴴ := by simp only [Matrix.mul_assoc]
        _ = _ := by rw [hunitary]; simp [Matrix.mul_assoc]
    rw [hid, tr, htrace]
    exact hpeak
  have hupper (g : G) : U g * τ * (U g)ᴴ ≤
      p₁ • (1 : Matrix H H ℂ) + (p₀ - p₁) • (U g * P * (U g)ᴴ) := by
    have hright : U g * (U g)ᴴ = 1 := by
      rw [← inverse_eq_conjTranspose U hunitary, ← map_mul, mul_inv_cancel, map_one]
    have h := (Matrix.le_iff.mp hspec).mul_mul_conjTranspose_same (U g)
    apply Matrix.le_iff.mpr
    simpa only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_add, Matrix.add_mul,
      Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, hright] using h
  exact compact_orbit_memory_bound μ E D hE hD hEt hDt
    (fun g => U g * P * (U g)ᴴ) (fun g => U g * τ * (U g)ᴴ)
    (fun g => hP.mul_mul_conjTranspose_same (U g))
    (fun g => (htrace P g).trans hPt)
    (fun g => hτ.mul_mul_conjTranspose_same (U g))
    (horbitc P) (horbitc τ)
    (compact_trace_one_unitary_twirl μ U hU hunitary P hPt)
    hgap rfl hpair hupper

/-- The manuscript's fixed spectral constant can replace the individual
spectral gap in the concrete compact-orbit memory bound. -/
theorem irreducible_orbit_memory_bound_gammaX [Nonempty H]
    {d r : ℕ} (s : FixedSpectrum d r)
    (μ : Measure G) [IsMulLeftInvariant μ] [IsProbabilityMeasure μ]
    (U : G →* Matrix H H ℂ) (hU : Continuous U)
    (hunitary : ∀ g, (U g)ᴴ * U g = 1)
    [Representation.IsIrreducible (matrixRepresentation U)]
    (E : Matrix H H ℂ →ₗ[ℝ] Matrix M M ℂ)
    (D : Matrix M M ℂ →ₗ[ℝ] Matrix H H ℂ)
    (hE : ∀ A, A.PosSemidef → (E A).PosSemidef)
    (hD : ∀ A, A.PosSemidef → (D A).PosSemidef)
    (hEt : ∀ A, (E A).trace = A.trace)
    (hDt : ∀ A, (D A).trace = A.trace)
    (P τ : Matrix H H ℂ) (hP : P.PosSemidef) (hPt : P.trace = 1) (hτ : τ.PosSemidef)
    {p₀ p₁ : ℝ} (htop : s.spectralProduct ≤ p₀) (hnext : p₁ ≤ s.qx * p₀)
    (hpeak : tr (P * τ) = p₀)
    (hspec : τ ≤ p₁ • (1 : Matrix H H ℂ) + (p₀ - p₁) • P) :
    (Fintype.card H : ℝ) * (1 -
      (∫ g, traceDistance (D (E (U g * τ * (U g)ᴴ))) (U g * τ * (U g)ᴴ) ∂μ) /
        s.gammaX) ≤ (Fintype.card M : ℝ) := by
  apply s.memory_bound_with_gammaX (Nat.cast_nonneg _)
    (integral_nonneg (fun _ => traceDistance_nonneg _ _))
    (s.gammaX_le_eigenvalue_gap htop hnext)
  exact irreducible_orbit_memory_bound μ U hU hunitary E D hE hD hEt hDt P τ hP hPt hτ
    (s.eigenvalue_gap_pos htop hnext) hpeak hspec

end CompactGroup

section ConverseBridge

open MeasureTheory.Measure FreeEntropy.Twirling Filter
open scoped Topology

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [MeasurableSpace G] [BorelSpace G]
  {d r : ℕ}

/-- Concrete data of a compression code for one irreducible orbit. The
spectral assumptions concern actual matrices; there is no assumed memory
inequality or abstract error-testing law in this structure. -/
structure OrbitCode (s : FixedSpectrum d r) (G : Type*) [Group G] [TopologicalSpace G]
    (target memory : ℕ) where
  U : G →* Matrix (Fin target) (Fin target) ℂ
  continuous_U : Continuous U
  unitary : ∀ g, (U g)ᴴ * U g = 1
  irreducible : Representation.IsIrreducible (matrixRepresentation U)
  encoder : Channels.MatrixChannel (Fin target) (Fin memory)
  decoder : Channels.MatrixChannel (Fin memory) (Fin target)
  state : Matrix (Fin target) (Fin target) ℂ
  state_positive : state.PosSemidef
  state_trace_one : state.trace = 1
  peak : Matrix (Fin target) (Fin target) ℂ
  peak_positive : peak.PosSemidef
  peak_trace_one : peak.trace = 1
  top : ℝ
  second : ℝ
  peak_overlap : tr (peak * state) = top
  spectral_upper : state ≤ second • (1 : Matrix (Fin target) (Fin target) ℂ) +
    (top - second) • peak
  top_lower : s.spectralProduct ≤ top
  next_upper : second ≤ s.qx * top

/-- The actual average recovery error of a concrete orbit code. -/
noncomputable def OrbitCode.averageError {s : FixedSpectrum d r} {target memory : ℕ}
    (C : OrbitCode s G target memory) (μ : Measure G) : ℝ :=
  ∫ g, traceDistance
    (C.decoder.toFun (C.encoder.toFun (C.U g * C.state * (C.U g)ᴴ)))
    (C.U g * C.state * (C.U g)ᴴ) ∂μ

theorem OrbitCode.memory_bound {s : FixedSpectrum d r} {target memory : ℕ}
    (C : OrbitCode s G target memory) (μ : Measure G)
    [IsMulLeftInvariant μ] [IsProbabilityMeasure μ] (htarget : 0 < target) :
    (target : ℝ) * (1 - C.averageError μ / s.gammaX) ≤ (memory : ℝ) := by
  letI : Nonempty (Fin target) := ⟨⟨0, htarget⟩⟩
  letI : Representation.IsIrreducible (matrixRepresentation C.U) := C.irreducible
  have h := irreducible_orbit_memory_bound_gammaX s μ C.U C.continuous_U C.unitary
    C.encoder.toRealLinearMap C.decoder.toRealLinearMap
    C.encoder.positive C.decoder.positive
    C.encoder.trace_preserving C.decoder.trace_preserving
    C.peak C.state C.peak_positive C.peak_trace_one C.state_positive
    C.top_lower C.next_upper C.peak_overlap C.spectral_upper
  simpa only [Fintype.card_fin, OrbitCode.averageError, Channels.MatrixChannel.toRealLinearMap,
    LinearMap.coe_mk, AddHom.coe_mk] using h

/-- Theorem 1's converse from concrete irreducible orbit codes. The finite
memory bound is proved above from matrices, CPTP channels, actual Haar error,
and spectral data; it is not an input to this asymptotic theorem. The remaining
error comparison is the transfer from the original source code to the orbit. -/
theorem theorem1_converse_of_compact_orbit_codes
    (s : FixedSpectrum d r) (memory target : ℕ → ℕ) (δ e : ℕ → ℝ)
    (μ : Measure G) [IsMulLeftInvariant μ] [IsProbabilityMeasure μ]
    (C : ∀ n, OrbitCode s G (target n) (memory n))
    (hdim : ∀ᶠ n in atTop,
      (target n : ℝ) = Weyl.activeProduct d r (s.targetRow n))
    (htarget : ∀ n, 0 < target n)
    (hδ : Tendsto δ atTop (𝓝 0)) (he : Asymptotics.IsBigO atTop e Weyl.errorScale)
    (herror : ∀ᶠ n in atTop, (C n).averageError μ ≤ δ n + e n) :
    (0 : EReal) ≤ liminf
      (fun n => ((Real.logb 2 (memory n) - Weyl.qmdl d r s.eigenvalue n : ℝ) : EReal)) atTop := by
  apply theorem1_converse_with_spectrum_gap s memory target δ e hdim htarget hδ he
  filter_upwards [herror] with n hn
  have hb := (C n).memory_bound μ (htarget n)
  have hratio := div_le_div_of_nonneg_right hn s.gammaX_pos.le
  have hcoef : 1 - (δ n + e n) / s.gammaX ≤ 1 - (C n).averageError μ / s.gammaX := by
    linarith
  exact (mul_le_mul_of_nonneg_left hcoef (Nat.cast_nonneg (target n))).trans hb

end ConverseBridge

end FreeEntropy.OrbitTraceDistance
