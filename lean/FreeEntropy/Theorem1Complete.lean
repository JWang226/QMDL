/-
Copyright (c) 2026 Free Entropy formalization contributors.
See LICENSE and NOTICE in the repository root for license and attribution.
-/

import FreeEntropy.PhysicalCloningAccuracy
import FreeEntropy.PhysicalUniformError
import FreeEntropy.OneDimensionalSource

/-! Theorem 1 for the actual known-spectrum physical tensor source, in
every dimension and rank. Both the code and its precise memory formula
are constructed; the converse assumes only vanishing reconstruction error. -/
noncomputable section
open Matrix Filter
open scoped Topology
namespace FreeEntropy
open Channels SchurWeyl ExteriorRepresentation
set_option backward.isDefEq.respectTransparency false
variable {d r : ℕ}

/-- Theorem 1, achievability: actual orbit-independent CPTP codes with the
exact additive memory constant and vanishing worst-case trace error. -/
theorem theorem1_achievability (s : FixedSpectrum d r) :
    ∃ memory : ℕ → ℕ,
      ∃ E : ∀ n, MatrixChannel (Fin n → Fin d) (Fin (memory n)),
      ∃ D : ∀ n, MatrixChannel (Fin (memory n)) (Fin n → Fin d),
        Tendsto (fun n => Real.logb 2 (memory n) - Weyl.qmdl d r s.eigenvalue n) atTop (𝓝 0) ∧
        Asymptotics.IsBigO atTop (fun n => mixedWorstError s n (E n) (D n)) Weyl.errorScale ∧
        Tendsto (fun n => mixedWorstError s n (E n) (D n)) atTop (𝓝 0) := by
  by_cases hd : 2 ≤ d
  · refine ⟨targetCanonicalDimension s, mixedEncoder s, mixedDecoder s, ?_⟩
    exact theorem1_physical_achievability_of_comparison s hd (mixedEncoder s) (mixedDecoder s)
      (mixedComparisonError s hd) (mixedComparisonError s hd)
      (mixedEncoder_error_eventually s hd) (mixedDecoder_error_eventually s hd)
      ((mixedComparisonError_isBigO s hd).add (mixedComparisonError_isBigO s hd))
  · have hd1 : d = 1 := by have := s.rank_pos; have := s.rank_le; omega
    subst d
    refine ⟨fun _ => 1, scalarSourceEncoder, scalarSourceDecoder, ?_⟩
    simpa only [Nat.cast_one] using theorem1_scalar_achievability s

/-- Theorem 1, converse: every actual physical code whose Haar-average
reconstruction error vanishes obeys the exact qmdl liminf bound. -/
theorem theorem1_converse (s : FixedSpectrum d r) (memory : ℕ → ℕ)
    (E : ∀ n, MatrixChannel (Fin n → Fin d) (Fin (memory n)))
    (D : ∀ n, MatrixChannel (Fin (memory n)) (Fin n → Fin d))
    (herror : Tendsto (fun n => mixedAverageError s n (E n) (D n)) atTop (𝓝 0)) :
    (0 : EReal) ≤ liminf
      (fun n => ((Real.logb 2 (memory n) - Weyl.qmdl d r s.eigenvalue n : ℝ) : EReal)) atTop := by
  by_cases hd : 2 ≤ d
  · exact theorem1_physical_converse_of_comparison s hd memory E D
      (mixedEncoder s) (mixedDecoder s) (mixedComparisonError s hd) (mixedComparisonError s hd)
      (mixedEncoder_error_eventually s hd) (mixedDecoder_error_eventually s hd)
      ((mixedComparisonError_isBigO s hd).add (mixedComparisonError_isBigO s hd)) herror
  · have hd1 : d = 1 := by have := s.rank_pos; have := s.rank_le; omega
    subst d
    exact theorem1_scalar_converse s memory E

/-- The original worst-case reliability criterion implies the same lower
bound; no average-error or transfer estimate is a supplied premise. -/
theorem theorem1_converse_of_uniform (s : FixedSpectrum d r) (memory : ℕ → ℕ)
    (E : ∀ n, MatrixChannel (Fin n → Fin d) (Fin (memory n)))
    (D : ∀ n, MatrixChannel (Fin (memory n)) (Fin n → Fin d))
    (herror : Tendsto (fun n => mixedWorstError s n (E n) (D n)) atTop (𝓝 0)) :
    (0 : EReal) ≤ liminf
      (fun n => ((Real.logb 2 (memory n) - Weyl.qmdl d r s.eigenvalue n : ℝ) : EReal)) atTop :=
  theorem1_converse s memory E D (mixedAverageError_tendsto_of_uniform s memory E D herror)

end FreeEntropy
