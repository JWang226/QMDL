/-
Copyright (c) 2026 Free Entropy formalization contributors.
See LICENSE and NOTICE in the repository root for license and attribution.
-/

import FreeEntropy.TraceDistance
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Algebra.Star.StarProjection
import Mathlib.Algebra.Order.Star.Basic

/-!
# Casimir gaps control trace deficits of actual projections

The error estimates needed for cloning require averaged trace deficits.
These follow directly from a spectral-gap operator inequality and Casimir
compression. No estimate of the norm of the difference of projections is
assumed. Equal projection traces transfer the reverse deficit to the forward
one by cyclicity of the trace.
-/

open scoped MatrixOrder ComplexOrder BigOperators
open Matrix
open FreeEntropy.OrbitMemory

namespace FreeEntropy.CasimirTrace

set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false

variable {H : Type*} [Fintype H] [DecidableEq H]

/-- The forward trace deficit of projections P and Q. -/
noncomputable def traceDeficit (P Q : Matrix H H ℂ) : ℝ := tr (P - P * Q * P)

theorem projection_pos {P : Matrix H H ℂ} (hP : IsStarProjection P) : P.PosSemidef :=
  hP.nonneg.posSemidef

/-- A projection's missing overlap is a positive matrix. -/
theorem projection_deficit_pos {P Q : Matrix H H ℂ}
    (hP : IsStarProjection P) (hQ : IsStarProjection Q) : (P - P * Q * P).PosSemidef := by
  have h := hQ.one_sub_nonneg.posSemidef.mul_mul_conjTranspose_same P
  simpa only [← Matrix.star_eq_conjTranspose, hP.isSelfAdjoint.star_eq,
    Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, hP.isIdempotentElem.eq] using h

theorem projection_sandwich_pos {P Q : Matrix H H ℂ}
    (hP : IsStarProjection P) (hQ : IsStarProjection Q) : (P * Q * P).PosSemidef := by
  simpa only [← Matrix.star_eq_conjTranspose, hP.isSelfAdjoint.star_eq] using
    (projection_pos hQ).mul_mul_conjTranspose_same P

/-- Cyclicity removes one copy of a projection inside the trace. -/
theorem trace_projection_sandwich {P : Matrix H H ℂ} (hP : IsStarProjection P)
    (A : Matrix H H ℂ) : tr (P * A * P) = tr (P * A) := by
  unfold tr
  rw [Matrix.trace_mul_cycle, hP.isIdempotentElem.eq]

theorem traceDeficit_eq {P Q : Matrix H H ℂ} (hP : IsStarProjection P) :
    traceDeficit P Q = tr P - tr (P * Q) := by
  unfold traceDeficit
  rw [show tr (P - P * Q * P) = tr P - tr (P * Q * P) by
    simp only [tr, Matrix.trace_sub, Complex.sub_re]]
  rw [trace_projection_sandwich hP]

theorem traceDeficit_nonneg {P Q : Matrix H H ℂ}
    (hP : IsStarProjection P) (hQ : IsStarProjection Q) : 0 ≤ traceDeficit P Q :=
  (projection_deficit_pos hP hQ).trace_nonneg.1

theorem traceDeficit_le_trace {P Q : Matrix H H ℂ}
    (hP : IsStarProjection P) (hQ : IsStarProjection Q) : traceDeficit P Q ≤ tr P := by
  have h := (projection_sandwich_pos hP hQ).trace_nonneg.1
  simp only [Complex.zero_re] at h
  unfold traceDeficit tr
  rw [Matrix.trace_sub, Complex.sub_re]
  linarith

/-- The two trace deficits differ exactly by the projection traces. -/
theorem traceDeficit_sub_reverse {P Q : Matrix H H ℂ}
    (hP : IsStarProjection P) (hQ : IsStarProjection Q) :
    traceDeficit P Q - traceDeficit Q P = tr P - tr Q := by
  rw [traceDeficit_eq hP, traceDeficit_eq hQ]
  have h : tr (P * Q) = tr (Q * P) := congrArg Complex.re (Matrix.trace_mul_comm P Q)
  rw [h]
  ring

/-- Equal projection traces give equal forward and reverse trace deficits. -/
theorem traceDeficit_eq_reverse_of_trace_eq {P Q : Matrix H H ℂ}
    (hP : IsStarProjection P) (hQ : IsStarProjection Q) (htr : tr P = tr Q) :
    traceDeficit P Q = traceDeficit Q P := by
  have h := traceDeficit_sub_reverse hP hQ
  rw [htr] at h
  linarith

/-- The real trace preserves the Loewner order. -/
theorem trace_mono {A B : Matrix H H ℂ} (h : A ≤ B) : tr A ≤ tr B := by
  have ht := (Matrix.le_iff.mp h).trace_nonneg.1
  simpa only [tr, Matrix.trace_sub, Complex.sub_re, Complex.zero_re, sub_nonneg] using ht

/-- A gap above P and an upper bound on compression by Q control the reverse
trace deficit. Neither equal rank nor an operator-norm bound is required. -/
theorem reverse_traceDeficit_le_of_gap
    {P Q A : Matrix H H ℂ} (hQ : IsStarProjection Q)
    {gap deficit : ℝ} (hgap : 0 < gap)
    (hA : gap • (1 - P) ≤ A) (hcomp : Q * A * Q ≤ deficit • Q) :
    traceDeficit Q P ≤ (deficit / gap) * tr Q := by
  have ht := trace_mul_mono (projection_pos hQ) hA
  have hc := trace_mono hcomp
  rw [trace_projection_sandwich hQ, tr_smul] at hc
  have hleft : tr (Q * (gap • (1 - P))) = gap * traceDeficit Q P := by
    rw [Matrix.mul_smul, tr_smul, Matrix.mul_sub, Matrix.mul_one, traceDeficit_eq hQ]
    simp only [tr, Matrix.trace_sub, Complex.sub_re]
  rw [hleft] at ht
  have hprod := ht.trans hc
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ hgap).mpr
  nlinarith

/-- The exact Casimir compression equation implies the reverse trace bound. -/
theorem reverse_traceDeficit_le_of_compression
    {P Q A : Matrix H H ℂ} (hQ : IsStarProjection Q)
    {gap deficit : ℝ} (hgap : 0 < gap)
    (hA : gap • (1 - P) ≤ A) (hcomp : Q * A * Q = deficit • Q) :
    traceDeficit Q P ≤ (deficit / gap) * tr Q :=
  reverse_traceDeficit_le_of_gap hQ hgap hA hcomp.le

/-- Equal traces transfer the Casimir estimate to the forward deficit. -/
theorem forward_traceDeficit_le_of_gap
    {P Q A : Matrix H H ℂ} (hP : IsStarProjection P) (hQ : IsStarProjection Q)
    (htr : tr P = tr Q) {gap deficit : ℝ} (hgap : 0 < gap)
    (hA : gap • (1 - P) ≤ A) (hcomp : Q * A * Q ≤ deficit • Q) :
    traceDeficit P Q ≤ (deficit / gap) * tr P := by
  rw [traceDeficit_eq_reverse_of_trace_eq hP hQ htr, htr]
  exact reverse_traceDeficit_le_of_gap hQ hgap hA hcomp

/-- The simultaneous forward/reverse estimates needed for cloning, clamped
by the trivial projection trace bound. -/
theorem traceDeficits_le_min_of_compression
    {P Q A : Matrix H H ℂ} (hP : IsStarProjection P) (hQ : IsStarProjection Q)
    (htr : tr P = tr Q) {gap deficit : ℝ} (hgap : 0 < gap)
    (hA : gap • (1 - P) ≤ A) (hcomp : Q * A * Q = deficit • Q) :
    traceDeficit P Q ≤ min 1 (deficit / gap) * tr P ∧
      traceDeficit Q P ≤ min 1 (deficit / gap) * tr Q := by
  have hf := forward_traceDeficit_le_of_gap hP hQ htr hgap hA hcomp.le
  have hr := reverse_traceDeficit_le_of_compression hQ hgap hA hcomp
  rcases le_total 1 (deficit / gap) with h | h
  · rw [min_eq_left h, one_mul, one_mul]
    exact ⟨traceDeficit_le_trace hP hQ, traceDeficit_le_trace hQ hP⟩
  · rw [min_eq_right h]
    exact ⟨hf, hr⟩

/-- The Casimir gap may be restricted to the relevant total-weight sector.
Only the source projector's support in that sector is needed. -/
theorem reverse_traceDeficit_le_of_local_gap
    {P Q S A : Matrix H H ℂ} (hQ : IsStarProjection Q)
    (hsupport : Q * S * Q = Q)
    {gap deficit : ℝ} (hgap : 0 < gap)
    (hA : gap • (S - P) ≤ A) (hcomp : Q * A * Q ≤ deficit • Q) :
    traceDeficit Q P ≤ (deficit / gap) * tr Q := by
  have ht := trace_mul_mono (projection_pos hQ) hA
  have hc := trace_mono hcomp
  rw [trace_projection_sandwich hQ, tr_smul] at hc
  have hs : tr (Q * S) = tr Q := by
    rw [← trace_projection_sandwich hQ S, hsupport]
  have hleft : tr (Q * (gap • (S - P))) = gap * traceDeficit Q P := by
    rw [Matrix.mul_smul, tr_smul, Matrix.mul_sub, traceDeficit_eq hQ]
    rw [show tr (Q * S - Q * P) = tr (Q * S) - tr (Q * P) by
      simp only [tr, Matrix.trace_sub, Complex.sub_re], hs]
  rw [hleft] at ht
  have hprod := ht.trans hc
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ hgap).mpr
  nlinarith

/-- Equal shallow multiplicities transfer a localized Casimir gap estimate
from the source trace deficit to the target trace deficit. -/
theorem forward_traceDeficit_le_of_local_gap
    {P Q S A : Matrix H H ℂ} (hP : IsStarProjection P) (hQ : IsStarProjection Q)
    (htr : tr P = tr Q) (hsupport : Q * S * Q = Q)
    {gap deficit : ℝ} (hgap : 0 < gap)
    (hA : gap • (S - P) ≤ A) (hcomp : Q * A * Q ≤ deficit • Q) :
    traceDeficit P Q ≤ (deficit / gap) * tr P := by
  rw [traceDeficit_eq_reverse_of_trace_eq hP hQ htr, htr]
  exact reverse_traceDeficit_le_of_local_gap hQ hsupport hgap hA hcomp

/-- Both deficits are bounded from a gap within a total-weight sector. -/
theorem traceDeficits_le_min_of_local_gap
    {P Q S A : Matrix H H ℂ} (hP : IsStarProjection P) (hQ : IsStarProjection Q)
    (htr : tr P = tr Q) (hsupport : Q * S * Q = Q)
    {gap deficit : ℝ} (hgap : 0 < gap)
    (hA : gap • (S - P) ≤ A) (hcomp : Q * A * Q ≤ deficit • Q) :
    traceDeficit P Q ≤ min 1 (deficit / gap) * tr P ∧
      traceDeficit Q P ≤ min 1 (deficit / gap) * tr Q := by
  have hf := forward_traceDeficit_le_of_local_gap hP hQ htr hsupport hgap hA hcomp
  have hr := reverse_traceDeficit_le_of_local_gap hQ hsupport hgap hA hcomp
  rcases le_total 1 (deficit / gap) with h | h
  · rw [min_eq_left h, one_mul, one_mul]
    exact ⟨traceDeficit_le_trace hP hQ, traceDeficit_le_trace hQ hP⟩
  · rw [min_eq_right h]
    exact ⟨hf, hr⟩

/-- The coordinate projection onto a set of actual spectral-basis indices. -/
def coordinateSector (s : Finset H) : Matrix H H ℂ :=
  diagonal (fun i => if i ∈ s then 1 else 0)

theorem coordinateSector_isStarProjection (s : Finset H) :
    IsStarProjection (coordinateSector s) := by
  rw [isStarProjection_iff']
  constructor
  · unfold coordinateSector
    rw [Matrix.diagonal_mul_diagonal]
    congr 1
    funext i
    split_ifs <;> simp
  · apply Matrix.isHermitian_diagonal_iff.mpr
    intro i
    change star (if i ∈ s then (1 : ℂ) else 0) = _
    split_ifs <;> simp

/-- The projection onto an arbitrary set of eigenspaces of a Hermitian
Casimir-deficit matrix, constructed from its actual eigenbasis. -/
noncomputable def eigenSector {A : Matrix H H ℂ} (hA : A.IsHermitian)
    (s : Finset H) : Matrix H H ℂ :=
  Unitary.conjStarAlgAut ℂ _ hA.eigenvectorUnitary (coordinateSector s)

theorem eigenSector_isStarProjection {A : Matrix H H ℂ} (hA : A.IsHermitian)
    (s : Finset H) : IsStarProjection (eigenSector hA s) :=
  (coordinateSector_isStarProjection s).map
    (Unitary.conjStarAlgAut ℂ _ hA.eigenvectorUnitary)

theorem eigenSector_trace {A : Matrix H H ℂ} (hA : A.IsHermitian)
    (s : Finset H) : (eigenSector hA s).trace = (s.card : ℂ) := by
  rw [eigenSector, Unitary.conjStarAlgAut_apply, Matrix.trace_mul_cycle,
    Unitary.coe_star_mul_self, Matrix.one_mul]
  simp [coordinateSector, Matrix.trace_diagonal]

/-- Actual eigenvalue inequalities establish the operator gap used above.
The selected spectral sector need only have nonnegative eigenvalues; every
excluded eigenvalue must lie above the claimed gap. -/
theorem spectral_gap_of_eigenvalues {A : Matrix H H ℂ} (hA : A.IsHermitian)
    (s : Finset H) (gap : ℝ)
    (hinside : ∀ i ∈ s, 0 ≤ hA.eigenvalues i)
    (houtside : ∀ i ∉ s, gap ≤ hA.eigenvalues i) :
    gap • (1 - eigenSector hA s) ≤ A := by
  let lower : H → ℝ := fun i => if i ∈ s then 0 else gap
  have hev (i : H) : lower i ≤ hA.eigenvalues i := by
    by_cases hi : i ∈ s
    · simpa [lower, hi] using hinside i hi
    · simpa [lower, hi] using houtside i hi
  have hD : (diagonal (fun i => (hA.eigenvalues i : ℂ)) -
      diagonal (fun i => (lower i : ℂ))).PosSemidef := by
    rw [Matrix.diagonal_sub]
    apply Matrix.PosSemidef.diagonal
    intro i
    change (0 : ℂ) ≤ (hA.eigenvalues i : ℂ) - (lower i : ℂ)
    rw [← Complex.ofReal_sub]
    exact Complex.zero_le_real.mpr (sub_nonneg.mpr (hev i))
  have hL : diagonal (fun i => (lower i : ℂ)) =
      gap • (1 - coordinateSector s) := by
    ext i j
    by_cases hij : i = j
    · subst j
      by_cases hi : i ∈ s <;>
        simp [lower, coordinateSector, Matrix.smul_apply, hi, Complex.real_smul]
    · simp [coordinateSector, Matrix.smul_apply, hij]
  have hdecomp : hA.eigenvectorUnitary.val *
      diagonal (fun i => (hA.eigenvalues i : ℂ)) * hA.eigenvectorUnitary.valᴴ = A := by
    simpa [Unitary.conjStarAlgAut_apply, Matrix.star_eq_conjTranspose, Function.comp_def]
      using hA.spectral_theorem.symm
  have hc := hD.mul_mul_conjTranspose_same hA.eigenvectorUnitary.val
  have hUU := Unitary.mul_star_self_of_mem hA.eigenvectorUnitary.prop
  apply Matrix.le_iff.mpr
  rw [Matrix.mul_sub, Matrix.sub_mul, hdecomp, hL] at hc
  simpa only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_sub, Matrix.sub_mul,
    Matrix.mul_one, ← Matrix.star_eq_conjTranspose, hUU,
    eigenSector, Unitary.conjStarAlgAut_apply, smul_sub] using hc

/-- Spectral data plus a compression equation now suffice for both trace
bounds; no free operator-gap hypothesis remains. -/
theorem traceDeficits_le_min_of_eigenvalues
    {A Q : Matrix H H ℂ} (hA : A.IsHermitian) (s : Finset H)
    (hQ : IsStarProjection Q) (gap deficit : ℝ) (hgap : 0 < gap)
    (hinside : ∀ i ∈ s, 0 ≤ hA.eigenvalues i)
    (houtside : ∀ i ∉ s, gap ≤ hA.eigenvalues i)
    (htrace : tr Q = (s.card : ℝ))
    (hcomp : Q * A * Q = deficit • Q) :
    traceDeficit (eigenSector hA s) Q ≤ min 1 (deficit / gap) * tr (eigenSector hA s) ∧
      traceDeficit Q (eigenSector hA s) ≤ min 1 (deficit / gap) * tr Q := by
  apply traceDeficits_le_min_of_compression (eigenSector_isStarProjection hA s) hQ
    ?_ hgap (spectral_gap_of_eigenvalues hA s gap hinside houtside) hcomp
  rw [htrace, tr, eigenSector_trace]
  simp

/-- A local Casimir gap needs spectral separation only within the chosen
total-weight sector. Other sectors merely need nonnegative deficit spectra. -/
theorem local_spectral_gap_of_eigenvalues {A : Matrix H H ℂ} (hA : A.IsHermitian)
    (s t : Finset H) (hst : s ⊆ t) (gap : ℝ)
    (hnonneg : ∀ i, 0 ≤ hA.eigenvalues i)
    (houtside : ∀ i ∈ t, i ∉ s → gap ≤ hA.eigenvalues i) :
    gap • (eigenSector hA t - eigenSector hA s) ≤ A := by
  let lower : H → ℝ := fun i => if i ∈ t then (if i ∈ s then 0 else gap) else 0
  have hev (i : H) : lower i ≤ hA.eigenvalues i := by
    by_cases hit : i ∈ t
    · by_cases his : i ∈ s
      · simpa [lower, hit, his] using hnonneg i
      · simpa [lower, hit, his] using houtside i hit his
    · simpa [lower, hit] using hnonneg i
  have hD : (diagonal (fun i => (hA.eigenvalues i : ℂ)) -
      diagonal (fun i => (lower i : ℂ))).PosSemidef := by
    rw [Matrix.diagonal_sub]
    apply Matrix.PosSemidef.diagonal
    intro i
    change (0 : ℂ) ≤ (hA.eigenvalues i : ℂ) - (lower i : ℂ)
    rw [← Complex.ofReal_sub]
    exact Complex.zero_le_real.mpr (sub_nonneg.mpr (hev i))
  have hL : diagonal (fun i => (lower i : ℂ)) =
      gap • (coordinateSector t - coordinateSector s) := by
    ext i j
    by_cases hij : i = j
    · subst j
      by_cases hit : i ∈ t
      · by_cases his : i ∈ s <;>
          simp [lower, coordinateSector, Matrix.smul_apply, hit, his, Complex.real_smul]
      · have his : i ∉ s := fun hi => hit (hst hi)
        simp [lower, coordinateSector, Matrix.smul_apply, hit, his]
    · simp [coordinateSector, Matrix.smul_apply, hij]
  have hdecomp : hA.eigenvectorUnitary.val *
      diagonal (fun i => (hA.eigenvalues i : ℂ)) * hA.eigenvectorUnitary.valᴴ = A := by
    simpa [Unitary.conjStarAlgAut_apply, Matrix.star_eq_conjTranspose, Function.comp_def]
      using hA.spectral_theorem.symm
  have hc := hD.mul_mul_conjTranspose_same hA.eigenvectorUnitary.val
  apply Matrix.le_iff.mpr
  rw [Matrix.mul_sub, Matrix.sub_mul, hdecomp, hL] at hc
  simpa only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_sub, Matrix.sub_mul,
    Matrix.mul_one, ← Matrix.star_eq_conjTranspose,
    eigenSector, Unitary.conjStarAlgAut_apply, smul_sub] using hc


/-- Local spectral data, support in the total-weight sector, and compression
imply both clamped trace-loss bounds. The spectral projection and its trace
are constructed, rather than supplied as operator-gap hypotheses. -/
theorem traceDeficits_le_min_of_local_eigenvalues
    {A Q : Matrix H H ℂ} (hA : A.IsHermitian) (s t : Finset H) (hst : s ⊆ t)
    (hQ : IsStarProjection Q) (gap deficit : ℝ) (hgap : 0 < gap)
    (hnonneg : ∀ i, 0 ≤ hA.eigenvalues i)
    (houtside : ∀ i ∈ t, i ∉ s → gap ≤ hA.eigenvalues i)
    (htrace : tr Q = (s.card : ℝ))
    (hsupport : Q * eigenSector hA t * Q = Q)
    (hcomp : Q * A * Q ≤ deficit • Q) :
    traceDeficit (eigenSector hA s) Q ≤ min 1 (deficit / gap) * tr (eigenSector hA s) ∧
      traceDeficit Q (eigenSector hA s) ≤ min 1 (deficit / gap) * tr Q := by
  apply traceDeficits_le_min_of_local_gap (eigenSector_isStarProjection hA s) hQ
    ?_ hsupport hgap (local_spectral_gap_of_eigenvalues hA s t hst gap hnonneg houtside) hcomp
  rw [htrace, tr, eigenSector_trace]
  simp

end FreeEntropy.CasimirTrace
