/-
Copyright (c) 2026 Free Entropy formalization contributors.
See LICENSE and NOTICE in the repository root for license and attribution.
-/

import Mathlib

/-! Independent expected definition in a separate compilation unit, preserving
Lean’s generated closed-proof names for strict upstream Comparator matching. -/
noncomputable section
open scoped BigOperators
namespace FreeEntropy.Weyl
def errorScale (n : ℕ) : ℝ := Real.logb 2 n / Real.sqrt n
end FreeEntropy.Weyl
