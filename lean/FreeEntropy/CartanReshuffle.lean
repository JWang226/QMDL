/-
Copyright (c) 2026 Free Entropy formalization contributors.
See LICENSE and NOTICE in the repository root for license and attribution.
-/

import FreeEntropy.LieDual

/-! Tensor-Hom adjunction in literal matrix coordinates. -/
noncomputable section
open Matrix
open scoped BigOperators Kronecker
namespace FreeEntropy.CartanChoi
open LieMatrixCasimir
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
variable {d : ℕ} {A B C : Type*} [Fintype A] [DecidableEq A]
  [Fintype B] [DecidableEq B] [Fintype C] [DecidableEq C]

/-- Contraction of the first tensor leg, without conjugation. -/
def reshuffle (V : Matrix (A × B) C ℂ) : Matrix B (A × C) ℂ :=
  fun b ac => V (ac.1, b) ac.2

def unreshuffle (F : Matrix B (A × C) ℂ) : Matrix (A × B) C ℂ :=
  fun ab c => F ab.2 (ab.1, c)

@[simp] theorem reshuffle_unreshuffle (F : Matrix B (A × C) ℂ) : reshuffle (unreshuffle F) = F := rfl
@[simp] theorem unreshuffle_reshuffle (V : Matrix (A × B) C ℂ) : unreshuffle (reshuffle V) = V := rfl

theorem reshuffle_injective : Function.Injective (reshuffle : Matrix (A × B) C ℂ → _) := by
  intro V W h
  exact congrArg unreshuffle h

@[simp] theorem reshuffle_smul (c : ℂ) (V : Matrix (A × B) C ℂ) :
    reshuffle (c • V) = c • reshuffle V := rfl

theorem tensor_mul_entry (R : Generators d A) (N : Generators d B)
    (V : Matrix (A × B) C ℂ) (i j : Fin d) (a : A) (b : B) (c : C) :
    ((R.tensor N).E i j * V) (a,b) c =
      (∑ a', R.E i j a a' * V (a',b) c) +
      (∑ b', N.E i j b b' * V (a,b') c) := by
  simp [Generators.tensor, Matrix.mul_apply, Fintype.sum_prod_type,
    Matrix.kronecker_apply, Matrix.one_apply, add_mul, Finset.sum_add_distrib,
    mul_ite, ite_mul]

theorem reshuffle_dual_tensor_entry (R : Generators d A) (S : Generators d C)
    (V : Matrix (A × B) C ℂ) (i j : Fin d) (a : A) (b : B) (c : C) :
    (reshuffle V * (R.dual.tensor S).E i j) b (a,c) =
      -(∑ a', R.E i j a a' * V (a',b) c) +
      (∑ c', V (a,b) c' * S.E i j c' c) := by
  simp [Generators.tensor, Generators.dual, reshuffle, Matrix.mul_apply,
    Fintype.sum_prod_type, Matrix.kronecker_apply, Matrix.one_apply,
    mul_add, Finset.sum_add_distrib, mul_ite, ite_mul, mul_comm,
    Finset.sum_neg_distrib]

/-- The explicit adjunction between a Cartan inclusion and its contraction. -/
theorem reshuffle_intertwines_iff (R : Generators d A) (N : Generators d B)
    (S : Generators d C) (V : Matrix (A × B) C ℂ) :
    (∀ i j, (R.tensor N).E i j * V = V * S.E i j) ↔
      (∀ i j, N.E i j * reshuffle V = reshuffle V * (R.dual.tensor S).E i j) := by
  constructor
  · intro h i j
    ext b ⟨a,c⟩
    have he := congrFun (congrFun (h i j) (a,b)) c
    rw [tensor_mul_entry] at he
    rw [reshuffle_dual_tensor_entry]
    change (∑ b', N.E i j b b' * V (a,b') c) = _
    simpa only [Matrix.mul_apply, sub_eq_add_neg, add_comm] using (eq_sub_of_add_eq' he)
  · intro h i j
    ext ⟨a,b⟩ c
    have he := congrFun (congrFun (h i j) b) (a,c)
    rw [reshuffle_dual_tensor_entry] at he
    rw [tensor_mul_entry]
    change (∑ b', N.E i j b b' * V (a,b') c) = _ at he
    simpa only [Matrix.mul_apply] using (add_eq_of_eq_sub' (show
      (∑ b', N.E i j b b' * V (a,b') c) =
      (∑ c', V (a,b) c' * S.E i j c' c) -
      (∑ a', R.E i j a a' * V (a',b) c) from by simpa [sub_eq_add_neg, add_comm] using he))

end FreeEntropy.CartanChoi
