/-
Copyright (c) 2026 Free Entropy formalization contributors.
See LICENSE and NOTICE in the repository root for license and attribution.
-/

import FreeEntropy.CartanChoi

/-! The Choi contraction is exactly the manuscript's partial-trace formula. -/
noncomputable section
open Matrix
open scoped BigOperators Kronecker
namespace FreeEntropy.CartanChoi
set_option backward.isDefEq.respectTransparency false
variable {A C : Type*} [Fintype A] [DecidableEq A] [Fintype C] [DecidableEq C]

/-- Partial trace over the input factor in input-dual × output coordinates. -/
def partialTraceInput (Y : Matrix (A × C) (A × C) ℂ) : Matrix C C ℂ :=
  fun c c' => ∑ a, Y (a, c) (a, c')

/-- Literal equality with `Tr_input[J (Xᵀ ⊗ I)]`, for arbitrary matrices. -/
theorem choiMap_eq_partialTraceInput (J : Matrix (A × C) (A × C) ℂ)
    (X : Matrix A A ℂ) :
    choiMap J X = partialTraceInput (J * (X.transpose ⊗ₖ (1 : Matrix C C ℂ))) := by
  ext c c'
  simp only [choiMap, partialTraceInput, Matrix.mul_apply, Fintype.sum_prod_type,
    Matrix.kronecker_apply, Matrix.transpose_apply, Matrix.one_apply, mul_ite,
    mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro a' _
  ring

end FreeEntropy.CartanChoi
