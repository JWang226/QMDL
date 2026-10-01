/-
Copyright (c) 2026 Free Entropy formalization contributors.
See LICENSE and NOTICE in the repository root for license and attribution.
-/

import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Order
import Mathlib.LinearAlgebra.Complex.Module

/-! Independent expected CPTP channel structure, elaborated in the original
foundational context so strict Comparator checks its generated constructor too. -/
open scoped BigOperators Matrix Kronecker ComplexOrder
open Matrix
noncomputable section
set_option autoImplicit false

namespace FreeEntropy.Channels
variable {ι α β : Type*} [Fintype ι] [Fintype α] [Fintype β]
def amplify {κ : Type*} (Φ : Matrix α α ℂ → Matrix β β ℂ)
    (X : Matrix (κ × α) (κ × α) ℂ) : Matrix (κ × β) (κ × β) ℂ :=
  fun a b => Φ (fun i j => X (a.1, i) (b.1, j)) a.2 b.2
structure MatrixChannel (α β : Type*) [Fintype α] [Fintype β] where
  toFun : Matrix α α ℂ → Matrix β β ℂ
  map_add : ∀ X Y, toFun (X + Y) = toFun X + toFun Y
  map_smul : ∀ (c : ℂ) X, toFun (c • X) = c • toFun X
  trace_preserving : ∀ X, Matrix.trace (toFun X) = Matrix.trace X
  positive : ∀ X, X.PosSemidef → (toFun X).PosSemidef
  completely_positive : ∀ (k : ℕ) (X : Matrix (Fin k × α) (Fin k × α) ℂ),
    X.PosSemidef → (amplify toFun X).PosSemidef
end FreeEntropy.Channels
