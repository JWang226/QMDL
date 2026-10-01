/-
Copyright (c) 2026 Free Entropy formalization contributors.
See LICENSE and NOTICE in the repository root for license and attribution.
-/

import FreeEntropy.CanonicalConverse
import FreeEntropy.PhysicalSchurProtocol
import FreeEntropy.QuantumTransfer

/-! Transfer of arbitrary codes on the literal mixed-state tensor source to
the actual padded canonical orbit. Every representation and spectral input
of the finite and asymptotic converse is constructed. -/
noncomputable section
open Matrix MeasureTheory MeasureTheory.Measure Filter
open scoped Topology Matrix.Norms.Elementwise ComplexOrder MatrixOrder
namespace FreeEntropy.SchurWeyl
open Channels TraceDistance ExteriorRepresentation
set_option backward.isDefEq.respectTransparency false
variable {d r : ℕ}

theorem physicalRepresentation_continuous (d n : ℕ) : Continuous (physicalRepresentation d n) := by
  apply continuous_pi
  intro x
  apply continuous_pi
  intro y
  change Continuous (fun U : Matrix.unitaryGroup (Fin d) ℂ => ∏ i : Fin n, U.val (x i) (y i))
  apply continuous_finset_prod
  intro i _
  exact (continuous_apply (y i)).comp ((continuous_apply (x i)).comp continuous_subtype_val)

def physicalSource (s : FixedSpectrum d r) (n : ℕ) (U : Matrix.unitaryGroup (Fin d) ℂ) :
    Matrix (Fin n → Fin d) (Fin n → Fin d) ℂ := TensorPowers.matrix n (physicalDensity s U)

theorem physicalSource_positive (s : FixedSpectrum d r) (n : ℕ)
    (U : Matrix.unitaryGroup (Fin d) ℂ) : (physicalSource s n U).PosSemidef :=
  TensorPowers.matrix_positive n (physicalDensity_positive s U)

theorem physicalSource_continuous (s : FixedSpectrum d r) (n : ℕ) :
    Continuous (physicalSource s n) := by
  have h := physicalRepresentation_continuous d n
  have he := (h.matrix_mul (continuous_const (y := TensorPowers.matrix n
    (Matrix.diagonal (fun j => (physicalSpectrum s j : ℂ)))))).matrix_mul h.matrix_conjTranspose
  have heq : physicalSource s n = fun U => physicalRepresentation d n U *
      TensorPowers.matrix n (Matrix.diagonal (fun j => (physicalSpectrum s j : ℂ))) *
        (physicalRepresentation d n U)ᴴ := by
    funext U
    exact TensorPowers.matrix_covariance n U.val _
  rw [heq]
  exact he

def mixedAverageError (s : FixedSpectrum d r) (n : ℕ)
    {B : Type*} [Fintype B] [DecidableEq B]
    (E : MatrixChannel (Fin n → Fin d) B) (D : MatrixChannel B (Fin n → Fin d)) : ℝ :=
  ∫ U, traceDistance (D.toFun (E.toFun (physicalSource s n U)))
    (physicalSource s n U) ∂UnitaryHaar.probabilityHaar (Fin d)

/-- Comparison channels transfer the actual Haar-average error of any
physical source code, with no representation-theoretic inputs. -/
theorem actual_transferred_average_error_le (s : FixedSpectrum d r) (hd : 2 ≤ d) (n : ℕ)
    {B : Type*} [Fintype B] [DecidableEq B]
    (A : MatrixChannel (Fin n → Fin d) (IrrepIndex (targetCanonicalRow s n)))
    (R : MatrixChannel (IrrepIndex (targetCanonicalRow s n)) (Fin n → Fin d))
    (E : MatrixChannel (Fin n → Fin d) B) (D : MatrixChannel B (Fin n → Fin d))
    (f g : ℝ)
    (hf : ∀ U, traceDistance (A.toFun (physicalSource s n U))
      (canonicalOrbitState s (targetCanonicalRow s n) U) ≤ f)
    (hr : ∀ U, traceDistance (R.toFun (canonicalOrbitState s (targetCanonicalRow s n) U))
      (physicalSource s n U) ≤ g) :
    canonicalAverageError s (targetCanonicalRow s n) (E.comp R) (A.comp D) ≤
      mixedAverageError s n E D + f + g :=
  QuantumTransfer.compact_transferred_average_error_le (UnitaryHaar.probabilityHaar (Fin d))
    A R E D (physicalSource s n) (canonicalOrbitState s (targetCanonicalRow s n))
    (physicalSource_continuous s n) (canonicalOrbitState_continuous s (targetCanonicalRow s n))
    (physicalSource_positive s n) (canonicalOrbitState_positive s (targetCanonicalRow s n) hd)
    (mixedAverageError s n E D) f g le_rfl hf hr

/-- The finite physical memory bound, after the actual canonical-orbit
dimension and spectral gap have both been proved. -/
theorem physical_memory_bound_of_comparison (s : FixedSpectrum d r) (hd : 2 ≤ d) (n : ℕ)
    {B : Type*} [Fintype B] [DecidableEq B]
    (A : MatrixChannel (Fin n → Fin d) (IrrepIndex (targetCanonicalRow s n)))
    (R : MatrixChannel (IrrepIndex (targetCanonicalRow s n)) (Fin n → Fin d))
    (E : MatrixChannel (Fin n → Fin d) B) (D : MatrixChannel B (Fin n → Fin d))
    (f g : ℝ)
    (hf : ∀ U, traceDistance (A.toFun (physicalSource s n U))
      (canonicalOrbitState s (targetCanonicalRow s n) U) ≤ f)
    (hr : ∀ U, traceDistance (R.toFun (canonicalOrbitState s (targetCanonicalRow s n) U))
      (physicalSource s n U) ≤ g) :
    (targetCanonicalDimension s n : ℝ) *
      (1 - (mixedAverageError s n E D + f + g) / (1 - s.qx) ^ (d.choose 2 + 1)) ≤
        (Fintype.card B : ℝ) := by
  have he := actual_transferred_average_error_le s hd n A R E D f g hf hr
  have hm := canonical_orbit_memory_bound s (targetCanonicalRow s n) hd
    (UnitaryHaar.probabilityHaar (Fin d)) (E.comp R) (A.comp D)
  have hgap : 0 < (1 - s.qx) ^ (d.choose 2 + 1) := pow_pos (sub_pos.mpr s.qx_lt_one) _
  exact (mul_le_mul_of_nonneg_left
    (sub_le_sub_left (div_le_div_of_nonneg_right he hgap.le) 1) (Nat.cast_nonneg _)).trans hm

/-- End-to-end asymptotic transfer for physical codes. The remaining
comparison estimates are the output of the constructed Schur protocol. -/
theorem theorem1_physical_converse_of_comparison (s : FixedSpectrum d r) (hd : 2 ≤ d)
    (memory : ℕ → ℕ)
    (E : ∀ n, MatrixChannel (Fin n → Fin d) (Fin (memory n)))
    (D : ∀ n, MatrixChannel (Fin (memory n)) (Fin n → Fin d))
    (A : ∀ n, MatrixChannel (Fin n → Fin d) (IrrepIndex (targetCanonicalRow s n)))
    (R : ∀ n, MatrixChannel (IrrepIndex (targetCanonicalRow s n)) (Fin n → Fin d))
    (f g : ℕ → ℝ)
    (hf : ∀ᶠ n in atTop, ∀ U, traceDistance ((A n).toFun (physicalSource s n U))
      (canonicalOrbitState s (targetCanonicalRow s n) U) ≤ f n)
    (hr : ∀ᶠ n in atTop, ∀ U, traceDistance ((R n).toFun (canonicalOrbitState s (targetCanonicalRow s n) U))
      (physicalSource s n U) ≤ g n)
    (hfg : Asymptotics.IsBigO atTop (fun n => f n + g n) Weyl.errorScale)
    (herror : Tendsto (fun n => mixedAverageError s n (E n) (D n)) atTop (𝓝 0)) :
    (0 : EReal) ≤ liminf
      (fun n => ((Real.logb 2 (memory n) - Weyl.qmdl d r s.eigenvalue n : ℝ) : EReal)) atTop := by
  apply theorem1_converse_of_quantum_estimates s memory (targetCanonicalDimension s)
    (fun n => mixedAverageError s n (E n) (D n)) (fun n => f n + g n)
    ((1 - s.qx) ^ (d.choose 2 + 1))
    (Eventually.of_forall (targetCanonicalDimension_weyl s)) (targetCanonicalDimension_pos s)
    (pow_pos (sub_pos.mpr s.qx_lt_one) _) herror hfg
  filter_upwards [hf, hr] with n hfn hrn
  simpa only [← add_assoc, Fintype.card_fin] using
    physical_memory_bound_of_comparison s hd n (A n) (R n) (E n) (D n) (f n) (g n) hfn hrn

end FreeEntropy.SchurWeyl
