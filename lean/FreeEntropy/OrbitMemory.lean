/-
Copyright (c) 2026 Free Entropy formalization contributors.
See LICENSE and NOTICE in the repository root for license and attribution.
-/

import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.Normed
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# The matrix and averaging core of the converse

This file proves the matrix argument of Proposition `compact_orbit_memory` in
`article.tex`, both for finite weighted orbits and for Bochner integrals. The
twirling identity, spectral upper bound, and trace-distance testing estimate
are explicit hypotheses. The modules `Twirling`, `TraceDistance`, `OrbitTraceDistance`, and
`OrbitEigenvalues` discharge these analytic and matrix inputs from genuine
irreducibility and actual eigenvalue bounds. No custom axioms are used.
-/

open scoped BigOperators MatrixOrder ComplexOrder
open Matrix

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 200000

namespace FreeEntropy.OrbitMemory

variable {H M G : Type*} [Fintype H] [DecidableEq H]
  [Fintype M] [DecidableEq M] [Fintype G]

/-- The real part of the matrix trace. -/
noncomputable def tr (A : Matrix H H ℂ) : ℝ := A.trace.re

omit [DecidableEq H] in
@[simp] theorem tr_add (A B : Matrix H H ℂ) : tr (A + B) = tr A + tr B := by
  simp [tr, Matrix.trace_add]

omit [DecidableEq H] in
@[simp] theorem tr_smul (r : ℝ) (A : Matrix H H ℂ) : tr (r • A) = r * tr A := by
  unfold tr
  rw [Matrix.trace_smul]
  simp

@[simp] theorem tr_one : tr (1 : Matrix H H ℂ) = Fintype.card H := by
  simp [tr]

omit [DecidableEq H] in
@[simp] theorem tr_sum (A : G → Matrix H H ℂ) : tr (∑ g, A g) = ∑ g, tr (A g) := by
  simp [tr, Matrix.trace_sum]

/-- A positive matrix of trace one is bounded above by the identity. -/
theorem state_le_one {A : Matrix H H ℂ} (hA : A.PosSemidef)
    (ht : A.trace = 1) : A ≤ 1 := by
  have hsum : ∑ i, hA.isHermitian.eigenvalues i = 1 := by
    have h := congrArg Complex.re (hA.isHermitian.trace_eq_sum_eigenvalues)
    simpa [ht] using h.symm
  have heig (i : H) : hA.isHermitian.eigenvalues i ≤ 1 := by
    rw [← hsum]
    exact Finset.single_le_sum (fun j _ => hA.eigenvalues_nonneg j) (Finset.mem_univ i)
  have hd : (1 - Matrix.diagonal (fun i => (hA.isHermitian.eigenvalues i : ℂ))).PosSemidef := by
    rw [← Matrix.diagonal_one, Matrix.diagonal_sub]
    apply Matrix.PosSemidef.diagonal
    intro i
    simpa using (Complex.zero_le_real.mpr (sub_nonneg.mpr (heig i)))
  have hp := hd.mul_mul_conjTranspose_same hA.isHermitian.eigenvectorUnitary.val
  apply Matrix.le_iff.mpr
  convert hp using 1
  conv_lhs => rw [hA.isHermitian.spectral_theorem]
  simp [Unitary.conjStarAlgAut_apply, Matrix.mul_sub, Matrix.sub_mul,
    ← Matrix.star_eq_conjTranspose, Function.comp_def]

/-- Positive matrices have a nonnegative trace pairing. -/
theorem trace_mul_nonneg {A B : Matrix H H ℂ}
    (hA : A.PosSemidef) (hB : B.PosSemidef) : 0 ≤ tr (A * B) := by
  obtain ⟨C, hC⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hA.nonneg
  have hp := hB.mul_mul_conjTranspose_same C
  have ht := hp.trace_nonneg
  rw [tr, hC]
  have heq : (star C * C * B).trace = (C * B * Cᴴ).trace := by
    rw [Matrix.trace_mul_cycle, Matrix.trace_mul_cycle]
    rfl
  rw [heq]
  exact ht.1

/-- Testing a matrix inequality against a positive observable preserves it. -/
theorem trace_mul_mono {P A B : Matrix H H ℂ}
    (hP : P.PosSemidef) (hAB : A ≤ B) : tr (P * A) ≤ tr (P * B) := by
  have h := trace_mul_nonneg hP (Matrix.le_iff.mp hAB)
  simpa [tr, Matrix.mul_sub, Matrix.trace_sub, Complex.sub_re] using h

omit [Fintype H] [DecidableEq H] [Fintype M] [DecidableEq M] in
/-- A real-linear map preserving positive matrices is monotone in the
Loewner order. -/
theorem positive_linear_mono
    (E : Matrix H H ℂ →ₗ[ℝ] Matrix M M ℂ)
    (hE : ∀ A, A.PosSemidef → (E A).PosSemidef)
    {A B : Matrix H H ℂ} (hAB : A ≤ B) : E A ≤ E B := by
  apply Matrix.le_iff.mpr
  have h := hE (B - A) (Matrix.le_iff.mp hAB)
  simpa only [map_sub] using h

/-- The operator inequality in the first display of the proposition's proof.
Only positivity and trace preservation of the encoder are required here. -/
theorem channel_spectral_upper
    (E : Matrix H H ℂ →ₗ[ℝ] Matrix M M ℂ)
    (D : Matrix M M ℂ →ₗ[ℝ] Matrix H H ℂ)
    (hE : ∀ A, A.PosSemidef → (E A).PosSemidef)
    (hD : ∀ A, A.PosSemidef → (D A).PosSemidef)
    (hEt : ∀ A, (E A).trace = A.trace)
    {P τ : Matrix H H ℂ} (hP : P.PosSemidef) (hPt : P.trace = 1)
    {p₁ γ : ℝ} (hγ : 0 ≤ γ)
    (hτ : τ ≤ p₁ • (1 : Matrix H H ℂ) + γ • P) :
    D (E τ) ≤ p₁ • D (E 1) + γ • D 1 := by
  have hEPpos : (E P).PosSemidef := hE P hP
  have hEP : E P ≤ (1 : Matrix M M ℂ) :=
    state_le_one (H := M) hEPpos ((hEt P).trans hPt)
  have hDE : D (E P) ≤ D (1 : Matrix M M ℂ) := positive_linear_mono D hD hEP
  have hscaled : γ • D (E P) ≤ γ • D (1 : Matrix M M ℂ) := by
    apply Matrix.le_iff.mpr
    rw [← smul_sub]
    exact (Matrix.le_iff.mp hDE).smul hγ
  calc
    D (E τ) ≤ D (E (p₁ • (1 : Matrix H H ℂ) + γ • P)) :=
      positive_linear_mono D hD (positive_linear_mono E hE hτ)
    _ = p₁ • D (E 1) + γ • D (E P) := by simp only [map_add, map_smul]
    _ ≤ p₁ • D (E 1) + γ • D 1 :=
      add_le_add le_rfl hscaled

/-- A finite weighted twirling identity implies the averaged trace identity. -/
theorem average_trace_pairing (w : G → ℝ) (P : G → Matrix H H ℂ)
    (htwirl : ∑ g, w g • P g = (Fintype.card H : ℝ)⁻¹ • (1 : Matrix H H ℂ))
    (A : Matrix H H ℂ) :
    (∑ g, w g * tr (P g * A)) = (Fintype.card H : ℝ)⁻¹ * tr A := by
  calc
    _ = tr ((∑ g, w g • P g) * A) := by
      simp [Matrix.sum_mul]
    _ = _ := by rw [htwirl]; simp

/-- Averaging the operator bound and using trace preservation gives exactly
the overlap upper bound in the converse. A finite weighted orbit replaces the
Haar integral; `htwirl` is the explicit Schur-lemma input. -/
theorem average_overlap_upper [Nonempty H]
    (E : Matrix H H ℂ →ₗ[ℝ] Matrix M M ℂ)
    (D : Matrix M M ℂ →ₗ[ℝ] Matrix H H ℂ)
    (hE : ∀ A, A.PosSemidef → (E A).PosSemidef)
    (hD : ∀ A, A.PosSemidef → (D A).PosSemidef)
    (hEt : ∀ A, (E A).trace = A.trace)
    (hDt : ∀ A, (D A).trace = A.trace)
    (w : G → ℝ) (hw : ∀ g, 0 ≤ w g)
    (P τ : G → Matrix H H ℂ)
    (hP : ∀ g, (P g).PosSemidef) (hPt : ∀ g, (P g).trace = 1)
    (htwirl : ∑ g, w g • P g = (Fintype.card H : ℝ)⁻¹ • (1 : Matrix H H ℂ))
    {p₁ γ : ℝ} (hγ : 0 ≤ γ)
    (hτ : ∀ g, τ g ≤ p₁ • (1 : Matrix H H ℂ) + γ • P g) :
    (∑ g, w g * tr (P g * D (E (τ g)))) ≤
      p₁ + γ * (Fintype.card M : ℝ) / (Fintype.card H : ℝ) := by
  have hdim : (Fintype.card H : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  calc
    _ ≤ ∑ g, w g * tr (P g * (p₁ • D (E 1) + γ • D 1)) := by
      apply Finset.sum_le_sum
      intro g _
      exact mul_le_mul_of_nonneg_left
        (trace_mul_mono (hP g) (channel_spectral_upper E D hE hD hEt (hP g) (hPt g) hγ (hτ g)))
        (hw g)
    _ = (Fintype.card H : ℝ)⁻¹ * tr (p₁ • D (E 1) + γ • D 1) :=
      average_trace_pairing w P htwirl _
    _ = p₁ + γ * (Fintype.card M : ℝ) / (Fintype.card H : ℝ) := by
      rw [tr_add, tr_smul, tr_smul]
      simp only [tr, hDt, hEt, Matrix.trace_one, Complex.natCast_re]
      field_simp [hdim]

/-- The resulting finite-orbit memory bound. The trace-distance testing step
is isolated in `htest`, so this is not a claim that the full compact-group
Haar-measure proposition has been formalized. -/
theorem finite_orbit_memory_bound [Nonempty H]
    (E : Matrix H H ℂ →ₗ[ℝ] Matrix M M ℂ)
    (D : Matrix M M ℂ →ₗ[ℝ] Matrix H H ℂ)
    (hE : ∀ A, A.PosSemidef → (E A).PosSemidef)
    (hD : ∀ A, A.PosSemidef → (D A).PosSemidef)
    (hEt : ∀ A, (E A).trace = A.trace)
    (hDt : ∀ A, (D A).trace = A.trace)
    (w : G → ℝ) (hw : ∀ g, 0 ≤ w g)
    (P τ : G → Matrix H H ℂ)
    (hP : ∀ g, (P g).PosSemidef) (hPt : ∀ g, (P g).trace = 1)
    (htwirl : ∑ g, w g • P g = (Fintype.card H : ℝ)⁻¹ • (1 : Matrix H H ℂ))
    {p₀ p₁ γ δ : ℝ} (hγ : 0 < γ) (hgap : γ = p₀ - p₁)
    (hτ : ∀ g, τ g ≤ p₁ • (1 : Matrix H H ℂ) + γ • P g)
    (htest : p₀ - δ ≤ ∑ g, w g * tr (P g * D (E (τ g)))) :
    (Fintype.card H : ℝ) * (1 - δ / γ) ≤ (Fintype.card M : ℝ) := by
  have hupper := average_overlap_upper E D hE hD hEt hDt w hw P τ hP hPt htwirl hγ.le hτ
  have hdim : 0 < (Fintype.card H : ℝ) := by exact_mod_cast Fintype.card_pos
  have hscalar := htest.trans hupper
  have hscaled := (le_div_iff₀ hdim).mp
    (show p₀ - δ - p₁ ≤ γ * (Fintype.card M : ℝ) / (Fintype.card H : ℝ) by linarith)
  apply (le_of_sub_nonneg ?_)
  apply (nonneg_of_mul_nonneg_left ?_ hγ)
  field_simp
  nlinarith

section Integral

open MeasureTheory
open scoped Matrix.Norms.Elementwise

variable {X : Type*} [MeasurableSpace X]

/-- The trace pairing as a continuous real-linear functional on matrices. -/
noncomputable def pairingCLM (A : Matrix H H ℂ) : Matrix H H ℂ →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap
    (Complex.reCLM.toLinearMap.comp
      ((Matrix.traceLinearMap H ℝ ℂ).comp (LinearMap.mulRight ℝ A)))

@[simp] theorem pairingCLM_apply (A B : Matrix H H ℂ) :
    pairingCLM A B = tr (B * A) := rfl

/-- The matrix-valued twirl passes through the trace pairing. This is a
Bochner integral identity, with integrability explicit. -/
theorem integral_trace_pairing (μ : Measure X) (P : X → Matrix H H ℂ)
    (hPi : Integrable P μ)
    (htwirl : ∫ x, P x ∂μ = (Fintype.card H : ℝ)⁻¹ • (1 : Matrix H H ℂ))
    (A : Matrix H H ℂ) :
    (∫ x, tr (P x * A) ∂μ) = (Fintype.card H : ℝ)⁻¹ * tr A := by
  have h := (pairingCLM A).integral_comp_comm hPi
  simpa only [pairingCLM_apply, htwirl, Matrix.smul_mul, Matrix.one_mul, tr_smul] using h

/-- The averaged overlap bound for a general measure. In the article the
measure is normalized Haar measure; irreducibility supplies `htwirl`.
All matrix positivity and trace-preservation steps are proved here. -/
theorem integral_overlap_upper [Nonempty H]
    (μ : Measure X)
    (E : Matrix H H ℂ →ₗ[ℝ] Matrix M M ℂ)
    (D : Matrix M M ℂ →ₗ[ℝ] Matrix H H ℂ)
    (hE : ∀ A, A.PosSemidef → (E A).PosSemidef)
    (hD : ∀ A, A.PosSemidef → (D A).PosSemidef)
    (hEt : ∀ A, (E A).trace = A.trace)
    (hDt : ∀ A, (D A).trace = A.trace)
    (P τ : X → Matrix H H ℂ)
    (hP : ∀ x, (P x).PosSemidef) (hPt : ∀ x, (P x).trace = 1)
    (hPi : Integrable P μ)
    (htwirl : ∫ x, P x ∂μ = (Fintype.card H : ℝ)⁻¹ • (1 : Matrix H H ℂ))
    {p₁ γ : ℝ} (hγ : 0 ≤ γ)
    (hτ : ∀ x, τ x ≤ p₁ • (1 : Matrix H H ℂ) + γ • P x)
    (hi : Integrable (fun x => tr (P x * D (E (τ x)))) μ) :
    (∫ x, tr (P x * D (E (τ x))) ∂μ) ≤
      p₁ + γ * (Fintype.card M : ℝ) / (Fintype.card H : ℝ) := by
  have hdim : (Fintype.card H : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hi' : Integrable (fun x => tr (P x * (p₁ • D (E 1) + γ • D 1))) μ := by
    simpa only [pairingCLM_apply] using
      (pairingCLM (p₁ • D (E 1) + γ • D 1)).integrable_comp hPi
  calc
    _ ≤ ∫ x, tr (P x * (p₁ • D (E 1) + γ • D 1)) ∂μ := by
      apply integral_mono hi hi'
      intro x
      exact trace_mul_mono (hP x)
        (channel_spectral_upper E D hE hD hEt (hP x) (hPt x) hγ (hτ x))
    _ = (Fintype.card H : ℝ)⁻¹ * tr (p₁ • D (E 1) + γ • D 1) :=
      integral_trace_pairing μ P hPi htwirl _
    _ = p₁ + γ * (Fintype.card M : ℝ) / (Fintype.card H : ℝ) := by
      rw [tr_add, tr_smul, tr_smul]
      simp only [tr, hDt, hEt, Matrix.trace_one, Complex.natCast_re]
      field_simp [hdim]

/-- The memory bound of Proposition `compact_orbit_memory`, conditional on
the explicit twirling, spectral-upper-bound, integrability, and testing
hypotheses. It applies in particular to normalized Haar measure once those
representation-theoretic and trace-distance inputs are supplied. -/
theorem integral_orbit_memory_bound [Nonempty H]
    (μ : Measure X)
    (E : Matrix H H ℂ →ₗ[ℝ] Matrix M M ℂ)
    (D : Matrix M M ℂ →ₗ[ℝ] Matrix H H ℂ)
    (hE : ∀ A, A.PosSemidef → (E A).PosSemidef)
    (hD : ∀ A, A.PosSemidef → (D A).PosSemidef)
    (hEt : ∀ A, (E A).trace = A.trace)
    (hDt : ∀ A, (D A).trace = A.trace)
    (P τ : X → Matrix H H ℂ)
    (hP : ∀ x, (P x).PosSemidef) (hPt : ∀ x, (P x).trace = 1)
    (hPi : Integrable P μ)
    (htwirl : ∫ x, P x ∂μ = (Fintype.card H : ℝ)⁻¹ • (1 : Matrix H H ℂ))
    {p₀ p₁ γ δ : ℝ} (hγ : 0 < γ) (hgap : γ = p₀ - p₁)
    (hτ : ∀ x, τ x ≤ p₁ • (1 : Matrix H H ℂ) + γ • P x)
    (hi : Integrable (fun x => tr (P x * D (E (τ x)))) μ)
    (htest : p₀ - δ ≤ ∫ x, tr (P x * D (E (τ x))) ∂μ) :
    (Fintype.card H : ℝ) * (1 - δ / γ) ≤ (Fintype.card M : ℝ) := by
  have hupper := integral_overlap_upper μ E D hE hD hEt hDt P τ hP hPt hPi htwirl hγ.le hτ hi
  have hdim : 0 < (Fintype.card H : ℝ) := by exact_mod_cast Fintype.card_pos
  have hscalar := htest.trans hupper
  have hscaled := (le_div_iff₀ hdim).mp
    (show p₀ - δ - p₁ ≤ γ * (Fintype.card M : ℝ) / (Fintype.card H : ℝ) by linarith)
  apply (le_of_sub_nonneg ?_)
  apply (nonneg_of_mul_nonneg_left ?_ hγ)
  field_simp
  nlinarith

end Integral

end FreeEntropy.OrbitMemory
