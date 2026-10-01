/-
Copyright (c) 2026 Free Entropy formalization contributors.
See LICENSE and NOTICE in the repository root for license and attribution.
-/

import FreeEntropy.ExteriorWeights

/-! Actual tensor products of the constructed exterior representations. -/
noncomputable section
open Matrix
open scoped BigOperators
namespace FreeEntropy.ExteriorRepresentation

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
set_option linter.unusedSectionVars false

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
  {B : ι → Type*} [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]

def productMatrix (A : ∀ a, Matrix (B a) (B a) ℂ) : Matrix (∀ a, B a) (∀ a, B a) ℂ :=
  fun x y => ∏ a, A a (x a) (y a)

theorem productMatrix_mul (A C : ∀ a, Matrix (B a) (B a) ℂ) :
    productMatrix (fun a => A a * C a) = productMatrix A * productMatrix C := by
  ext x y
  simp only [productMatrix, Matrix.mul_apply]
  rw [Fintype.prod_sum]
  simp only [Finset.prod_mul_distrib]

theorem productMatrix_adjoint (A : ∀ a, Matrix (B a) (B a) ℂ) :
    productMatrix (fun a => (A a)ᴴ) = (productMatrix A)ᴴ := by
  ext x y
  simp [productMatrix, Matrix.conjTranspose_apply]

theorem productMatrix_one : productMatrix (fun a => (1 : Matrix (B a) (B a) ℂ)) = 1 := by
  ext x y
  by_cases h : x = y
  · subst y
    simp [productMatrix]
  · have he : ∃ a, x a ≠ y a := by
      by_contra hn
      push_neg at hn
      exact h (funext hn)
    obtain ⟨a, ha⟩ := he
    rw [Matrix.one_apply_ne h]
    exact Finset.prod_eq_zero (Finset.mem_univ a) (by simp [Matrix.one_apply_ne ha])

theorem productMatrix_diagonal (z : ∀ a, B a → ℂ) :
    productMatrix (fun a => diagonal (z a)) = diagonal (fun x => ∏ a, z a (x a)) := by
  ext x y
  by_cases h : x = y
  · subst y
    simp [productMatrix]
  · have he : ∃ a, x a ≠ y a := by
      by_contra hn
      push_neg at hn
      exact h (funext hn)
    obtain ⟨a, ha⟩ := he
    rw [Matrix.diagonal_apply_ne _ h]
    exact Finset.prod_eq_zero (Finset.mem_univ a) (by simp [Matrix.diagonal_apply_ne _ ha])

theorem character_eq_weight_monomial {d k : ℕ} (z : Fin d → ℂ) (s : Index d k) :
    character z s = ∏ i : Fin d, z i ^ weight s i := by
  have hp : (∏ i : Fin k, z (enumerate s i)) = ∏ j ∈ s.val, z j := by
    apply Finset.prod_bij (fun i _ => enumerate s i)
    · exact fun i _ => mem_enumerate s i
    · intro i _ j _ he
      exact (enumerate s).injective he
    · intro j hj
      obtain ⟨i, hi⟩ := (Set.powersetCard.mem_range_ofFinEmbEquiv_symm_iff_mem s j).mpr hj
      exact ⟨i, Finset.mem_univ _, hi⟩
    · intro i _
      rfl
  rw [character, hp]
  simp only [weight, pow_ite, pow_one, pow_zero, ← Finset.prod_filter]
  congr 1
  ext i
  simp

variable {d : ℕ} (height : ι → ℕ)

def tensorMatrix (U : Matrix (Fin d) (Fin d) ℂ) :
    Matrix (TensorIndex (d := d) height) (TensorIndex (d := d) height) ℂ :=
  productMatrix (fun a => exteriorMatrix (height a) U)

theorem tensorMatrix_mul (U V : Matrix (Fin d) (Fin d) ℂ) :
    tensorMatrix height (U * V) = tensorMatrix height U * tensorMatrix height V := by
  simp only [tensorMatrix, exteriorMatrix_mul, productMatrix_mul]

theorem tensorMatrix_one : tensorMatrix height (1 : Matrix (Fin d) (Fin d) ℂ) = 1 := by
  simp only [tensorMatrix, exteriorMatrix_one, productMatrix_one]

theorem tensorMatrix_adjoint (U : Matrix (Fin d) (Fin d) ℂ) :
    tensorMatrix height Uᴴ = (tensorMatrix height U)ᴴ := by
  simp only [tensorMatrix, exteriorMatrix_adjoint, productMatrix_adjoint]

def tensorRepresentation : Matrix.unitaryGroup (Fin d) ℂ →*
    Matrix (TensorIndex (d := d) height) (TensorIndex (d := d) height) ℂ where
  toFun U := tensorMatrix height U.val
  map_one' := tensorMatrix_one height
  map_mul' U V := tensorMatrix_mul height U.val V.val

theorem tensorRepresentation_unitary (U : Matrix.unitaryGroup (Fin d) ℂ) :
    (tensorRepresentation height U)ᴴ * tensorRepresentation height U = 1 := by
  change (tensorMatrix height U.val)ᴴ * tensorMatrix height U.val = 1
  have hU : U.valᴴ * U.val = 1 := Matrix.UnitaryGroup.star_mul_self U
  rw [← tensorMatrix_adjoint, ← tensorMatrix_mul, hU, tensorMatrix_one]

theorem tensorMatrix_diagonal (z : Fin d → ℂ) :
    tensorMatrix height (diagonal z) =
      diagonal (fun x => ∏ i : Fin d, z i ^ tensorWeight height x i) := by
  simp only [tensorMatrix, exteriorMatrix_diagonal, productMatrix_diagonal,
    character_eq_weight_monomial]
  congr 1
  funext x
  rw [Finset.prod_comm]
  apply Finset.prod_congr rfl
  intro i _
  simp [tensorWeight, Finset.prod_pow_eq_pow_sum]

theorem tensorWeight_le (x : TensorIndex (d := d) height) (i : Fin d) :
    tensorWeight height x i ≤ Fintype.card ι := by
  calc
    _ ≤ ∑ a : ι, (1 : ℕ) := Finset.sum_le_sum (fun a _ => by simp [weight]; split <;> omega)
    _ = _ := by simp

theorem tensorRepresentation_continuous : Continuous (tensorRepresentation (d := d) height) := by
  apply continuous_pi
  intro x
  apply continuous_pi
  intro y
  change Continuous (fun U : Matrix.unitaryGroup (Fin d) ℂ =>
    ∏ a, exteriorMatrix (height a) U.val (x a) (y a))
  apply continuous_finset_prod
  intro a _
  exact (continuous_apply (y a)).comp ((continuous_apply (x a)).comp
    ((exteriorMatrix_continuous d (height a)).comp continuous_subtype_val))

end FreeEntropy.ExteriorRepresentation
