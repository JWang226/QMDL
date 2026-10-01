/-
Copyright (c) 2026 Free Entropy formalization contributors.
See LICENSE and NOTICE in the repository root for license and attribution.
-/

import FreeEntropy.OccupationSplit
import FreeEntropy.OccupationRepresentation

/-!
# Equivariance of the concrete symmetric Cartan isometry

The splitting matrix intertwines the actual tensor-power representations.
This follows by regrouping word coordinates and canceling the proved
occupation-basis isometry; no representation identity is assumed.
-/
noncomputable section
open scoped BigOperators Matrix Kronecker
open Matrix
namespace FreeEntropy.OccupationSplit
open Occupation
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
variable {d n m : ℕ}

theorem tensor_matrix_joinWords (A : Matrix (Fin d) (Fin d) ℂ)
    (w v : (Fin n → Fin d) × (Fin m → Fin d)) :
    TensorPowers.matrix (n + m) A (joinWords w) (joinWords v) =
      (TensorPowers.matrix n A ⊗ₖ TensorPowers.matrix m A) w v := by
  rcases w with ⟨w, w'⟩
  rcases v with ⟨v, v'⟩
  simp only [TensorPowers.matrix, Fin.prod_univ_add, joinWords_left, joinWords_right,
    Matrix.kronecker_apply]

theorem joinedBasis_intertwines (A : Matrix (Fin d) (Fin d) ℂ) :
    (TensorPowers.matrix n A ⊗ₖ TensorPowers.matrix m A) * joinedBasis =
      joinedBasis * symmetricMatrix (n := n + m) A := by
  ext w a
  have h := congrFun (congrFun (symmetricMatrix_intertwines (n := n + m) A) (joinWords w)) a
  simp only [Matrix.mul_apply] at h ⊢
  change (∑ v, (TensorPowers.matrix n A ⊗ₖ TensorPowers.matrix m A) w v *
      basis (joinWords v) a) = _
  simp only [← tensor_matrix_joinWords]
  rw [Equiv.sum_comp joinWords (fun v => TensorPowers.matrix (n + m) A (joinWords w) v * basis v a)]
  exact h

theorem productBasis_intertwines (A : Matrix (Fin d) (Fin d) ℂ) :
    (TensorPowers.matrix n A ⊗ₖ TensorPowers.matrix m A) * productBasis =
      productBasis * (symmetricMatrix (n := n) A ⊗ₖ symmetricMatrix (n := m) A) := by
  unfold productBasis
  rw [← Matrix.mul_kronecker_mul, symmetricMatrix_intertwines, symmetricMatrix_intertwines,
    Matrix.mul_kronecker_mul]

/-- Actual equivariance of the explicitly constructed symmetric-power embedding. -/
theorem split_intertwines (A : Matrix (Fin d) (Fin d) ℂ) :
    (symmetricMatrix (n := n) A ⊗ₖ symmetricMatrix (n := m) A) * split =
      split * symmetricMatrix (n := n + m) A := by
  have he : productBasis * ((symmetricMatrix (n := n) A ⊗ₖ symmetricMatrix (n := m) A) * split) =
      productBasis * (split * symmetricMatrix (n := n + m) A) := by
    rw [← Matrix.mul_assoc, ← productBasis_intertwines, Matrix.mul_assoc,
      productBasis_mul_split, joinedBasis_intertwines, ← Matrix.mul_assoc, productBasis_mul_split]
  have hh := congrArg (fun X => (productBasis (d := d) (n := n) (m := m))ᴴ * X) he
  simpa only [← Matrix.mul_assoc, productBasis_isometry, Matrix.one_mul] using hh

end FreeEntropy.OccupationSplit
