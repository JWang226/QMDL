/-
Copyright (c) 2026 Free Entropy formalization contributors.
See LICENSE and NOTICE in the repository root for license and attribution.
-/
import ComparatorChallenges.PhysicalInterface

/-! Independent expected statements. The explicit `sorry` is an intentional
Comparator challenge hole, never imported by or admitted in the proof library.
No target theorem or solution proposition is imported or aliased here. -/
noncomputable section
open Matrix Filter
open scoped Topology
namespace FreeEntropy
open Channels SchurWeyl
set_option backward.isDefEq.respectTransparency false
variable {d r : ℕ}

theorem theorem1_converse (s : FixedSpectrum d r) (memory : ℕ → ℕ)
    (E : ∀ n, MatrixChannel (Fin n → Fin d) (Fin (memory n)))
    (D : ∀ n, MatrixChannel (Fin (memory n)) (Fin n → Fin d))
    (herror : Tendsto (fun n => mixedAverageError s n (E n) (D n)) atTop (𝓝 0)) :
    (0 : EReal) ≤ liminf
      (fun n => ((Real.logb 2 (memory n) - Weyl.qmdl d r s.eigenvalue n : ℝ) : EReal)) atTop := by
  sorry

theorem theorem1_converse_of_uniform (s : FixedSpectrum d r) (memory : ℕ → ℕ)
    (E : ∀ n, MatrixChannel (Fin n → Fin d) (Fin (memory n)))
    (D : ∀ n, MatrixChannel (Fin (memory n)) (Fin n → Fin d))
    (herror : Tendsto (fun n => mixedWorstError s n (E n) (D n)) atTop (𝓝 0)) :
    (0 : EReal) ≤ liminf
      (fun n => ((Real.logb 2 (memory n) - Weyl.qmdl d r s.eigenvalue n : ℝ) : EReal)) atTop := by
  sorry

end FreeEntropy
