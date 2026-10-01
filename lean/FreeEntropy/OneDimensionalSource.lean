/-
Copyright (c) 2026 Free Entropy formalization contributors.
See LICENSE and NOTICE in the repository root for license and attribution.
-/

import FreeEntropy.PhysicalUniformError
import FreeEntropy.AtypicalChannels

/-! The dimension-one endpoint: a single known scalar state requires no
stored information. This also closes the small-dimension case of Theorem 1. -/
noncomputable section
open Matrix Filter
open scoped Topology ComplexOrder MatrixOrder
namespace FreeEntropy.SchurWeyl
open Channels TraceDistance ExteriorRepresentation
set_option backward.isDefEq.respectTransparency false

theorem trace_one_subsingleton_state {A : Type*} [Fintype A] [DecidableEq A] [Subsingleton A]
    (a : A) (X : Matrix A A ℂ) (hX : X.trace = 1) : X = SpectralProjector.coordinateProjection a := by
  letI : Unique A := { default := a, uniq := fun _ => Subsingleton.elim _ _ }
  have he : X a a = 1 := by simpa [Matrix.trace, Matrix.diag] using hX
  ext i j
  have hi : i = a := Subsingleton.elim _ _
  have hj : j = a := Subsingleton.elim _ _
  subst i
  subst j
  simpa [SpectralProjector.coordinateProjection] using he

def scalarSourceEncoder (n : ℕ) : MatrixChannel (Fin n → Fin 1) (Fin 1) :=
  AtypicalChannels.replacementChannel 0

def scalarSourceDecoder (n : ℕ) : MatrixChannel (Fin 1) (Fin n → Fin 1) :=
  AtypicalChannels.replacementChannel (fun _ => 0)

theorem scalarSource_roundtrip {r : ℕ} (s : FixedSpectrum 1 r) (n : ℕ)
    (U : Matrix.unitaryGroup (Fin 1) ℂ) :
    (scalarSourceDecoder n).toFun ((scalarSourceEncoder n).toFun (physicalSource s n U)) =
      physicalSource s n U := by
  rw [scalarSourceDecoder, AtypicalChannels.replacementChannel_state _ _
    (by rw [(scalarSourceEncoder n).trace_preserving, physicalSource_trace])]
  exact (trace_one_subsingleton_state _ _ (physicalSource_trace s n U)).symm

theorem scalarSource_worstError {r : ℕ} (s : FixedSpectrum 1 r) (n : ℕ) :
    mixedWorstError s n (scalarSourceEncoder n) (scalarSourceDecoder n) = 0 := by
  apply le_antisymm _ (mixedWorstError_nonneg _ _ _ _)
  apply mixedWorstError_le
  intro U
  rw [scalarSource_roundtrip]
  simp [traceDistance, traceNorm, OrbitMemory.tr]

theorem scalar_qmdl {r : ℕ} (s : FixedSpectrum 1 r) (n : ℕ) : Weyl.qmdl 1 r s.eigenvalue n = 0 := by
  have hr : r = 1 := by have := s.rank_pos; have := s.rank_le; omega
  subst r
  norm_num [Weyl.qmdl]

theorem theorem1_scalar_achievability {r : ℕ} (s : FixedSpectrum 1 r) :
    Tendsto (fun n => Real.logb 2 (1 : ℝ) - Weyl.qmdl 1 r s.eigenvalue n) atTop (𝓝 0) ∧
      Asymptotics.IsBigO atTop
        (fun n => mixedWorstError s n (scalarSourceEncoder n) (scalarSourceDecoder n)) Weyl.errorScale ∧
      Tendsto (fun n => mixedWorstError s n (scalarSourceEncoder n) (scalarSourceDecoder n)) atTop (𝓝 0) := by
  simp only [scalar_qmdl, Real.logb_one, sub_self, scalarSource_worstError]
  exact ⟨tendsto_const_nhds, Asymptotics.isBigO_zero _ _, tendsto_const_nhds⟩

theorem channel_target_nonempty {A B : Type*} [Fintype A] [Fintype B]
    (E : MatrixChannel A B) (X : Matrix A A ℂ) (hX : X.trace = 1) : Nonempty B := by
  by_contra h
  letI : IsEmpty B := not_nonempty_iff.mp h
  have ht := (E.trace_preserving X).trans hX
  simp [Matrix.trace] at ht

/-- A scalar source has zero qmdl. The converse holds for every physical
encoder, even without any reconstruction-error assumption. -/
theorem theorem1_scalar_converse {r : ℕ} (s : FixedSpectrum 1 r) (memory : ℕ → ℕ)
    (E : ∀ n, MatrixChannel (Fin n → Fin 1) (Fin (memory n))) :
    (0 : EReal) ≤ liminf
      (fun n => ((Real.logb 2 (memory n) - Weyl.qmdl 1 r s.eigenvalue n : ℝ) : EReal)) atTop := by
  apply nonnegative_ereal_liminf_of_eventual_lower_bound
  intro eta heta
  exact Eventually.of_forall (fun n => by
    have hne := channel_target_nonempty (E n) (physicalSource s n 1) (physicalSource_trace s n 1)
    have hm : 1 ≤ memory n := Fin.pos_iff_nonempty.mpr hne
    have hl : 0 ≤ Real.logb 2 (memory n) := Real.logb_nonneg (by norm_num) (by exact_mod_cast hm)
    rw [scalar_qmdl, sub_zero]
    linarith)

end FreeEntropy.SchurWeyl
