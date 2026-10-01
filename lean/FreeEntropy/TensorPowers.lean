/-
Copyright (c) 2026 Free Entropy formalization contributors.
See LICENSE and NOTICE in the repository root for license and attribution.
-/

import FreeEntropy.TraceDistance
import Mathlib.Analysis.Matrix.Order
import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# Actual tensor-power source matrices

The tensor power is defined entry by entry on words. Multiplication, adjoints,
positivity, trace normalization, unitary covariance, and pure-state tensor
vectors are proved directly from finite sums and products.
-/
noncomputable section
open scoped BigOperators MatrixOrder ComplexOrder
open Matrix
namespace FreeEntropy.TensorPowers
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
variable {H K L : Type*} [Fintype H] [Fintype K] [Fintype L]
  [DecidableEq H] [DecidableEq K] [DecidableEq L]

def matrix (n : ℕ) (A : Matrix H K ℂ) : Matrix (Fin n → H) (Fin n → K) ℂ :=
  fun x y => ∏ t, A (x t) (y t)

theorem matrix_mul (n : ℕ) (A : Matrix H K ℂ) (B : Matrix K L ℂ) :
    matrix n (A * B) = matrix n A * matrix n B := by
  ext x y
  simp only [matrix, Matrix.mul_apply]
  rw [Fintype.prod_sum]
  simp only [Finset.prod_mul_distrib]

theorem matrix_adjoint (n : ℕ) (A : Matrix H K ℂ) :
    matrix n Aᴴ = (matrix n A)ᴴ := by
  ext x y
  simp [matrix, Matrix.conjTranspose_apply]

theorem matrix_one (n : ℕ) : matrix n (1 : Matrix H H ℂ) = 1 := by
  ext x y
  by_cases h : x = y
  · subst y
    simp [matrix]
  · have he : ∃ t, x t ≠ y t := by
      by_contra hn
      push_neg at hn
      exact h (funext hn)
    obtain ⟨t, ht⟩ := he
    rw [Matrix.one_apply_ne h]
    exact Finset.prod_eq_zero (Finset.mem_univ t) (by simp [Matrix.one_apply_ne ht])

theorem matrix_trace (n : ℕ) (A : Matrix H H ℂ) :
    (matrix n A).trace = A.trace ^ n := by
  unfold Matrix.trace Matrix.diag matrix
  rw [← Fintype.prod_sum (fun (_t : Fin n) (i : H) => A i i)]
  simp

theorem matrix_positive (n : ℕ) {A : Matrix H H ℂ} (hA : A.PosSemidef) :
    (matrix n A).PosSemidef := by
  obtain ⟨B, hB⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hA.nonneg
  rw [hB]
  change (matrix n (Bᴴ * B)).PosSemidef
  rw [matrix_mul, matrix_adjoint]
  exact Matrix.posSemidef_conjTranspose_mul_self _

theorem matrix_state (n : ℕ) {A : Matrix H H ℂ} (hA : A.PosSemidef) (ht : A.trace = 1) :
    (matrix n A).PosSemidef ∧ (matrix n A).trace = 1 := by
  exact ⟨matrix_positive n hA, by rw [matrix_trace, ht, one_pow]⟩

theorem matrix_unitary (n : ℕ) {U : Matrix H H ℂ} (hU : Uᴴ * U = 1) :
    (matrix n U)ᴴ * matrix n U = 1 := by
  rw [← matrix_adjoint, ← matrix_mul, hU, matrix_one]

theorem matrix_covariance (n : ℕ) (U A : Matrix H H ℂ) :
    matrix n (U * A * Uᴴ) = matrix n U * matrix n A * (matrix n U)ᴴ := by
  rw [matrix_mul, matrix_mul, matrix_adjoint]

/-- The tensor vector of `n` identical pure-state vectors. -/
def vector (n : ℕ) (v : H → ℂ) : (Fin n → H) → ℂ := fun w => ∏ t, v (w t)

def pure (v : H → ℂ) : Matrix H H ℂ := fun i j => v i * star (v j)

theorem matrix_pure (n : ℕ) (v : H → ℂ) : matrix n (pure v) = pure (vector n v) := by
  ext x y
  simp [matrix, pure, vector, Finset.prod_mul_distrib]

theorem vector_action (n : ℕ) (U : Matrix H K ℂ) (v : K → ℂ) :
    matrix n U *ᵥ vector n v = vector n (U *ᵥ v) := by
  ext x
  simp only [Matrix.mulVec, dotProduct, matrix, vector, ← Finset.prod_mul_distrib]
  exact (Fintype.prod_sum (fun t k => U (x t) k * v k)).symm

/-- Tensor powers form an actual matrix monoid representation. -/
def representation (n : ℕ) {G : Type*} [Monoid G] (U : G →* Matrix H H ℂ) :
    G →* Matrix (Fin n → H) (Fin n → H) ℂ where
  toFun g := matrix n (U g)
  map_one' := by rw [map_one, matrix_one]
  map_mul' g h := by rw [map_mul, matrix_mul]

end FreeEntropy.TensorPowers
