/-
Copyright (c) 2026 Free Entropy formalization contributors.
See LICENSE and NOTICE in the repository root for license and attribution.
-/

import FreeEntropy.CyclicWeightHighest
import FreeEntropy.LieHighestUnitary
import FreeEntropy.CartanChannel

/-! Channel normalization follows directly from the actual Lie action and
highest cyclicity. No group representation or Schur-lemma input is needed. -/
noncomputable section
open Matrix
open scoped BigOperators Kronecker
namespace FreeEntropy.CartanBalance
open CartanChannel CartanLieCloning LieMatrixCasimir
set_option backward.isDefEq.respectTransparency false
variable {d : ℕ} {A B C : Type*} [Fintype A] [DecidableEq A]
  [Fintype B] [DecidableEq B] [Fintype C] [DecidableEq C]

theorem partialTrace_left (X : Matrix A A ℂ) (P : Matrix (A × B) (A × B) ℂ) :
    partialTrace ((X ⊗ₖ (1 : Matrix B B ℂ)) * P) = X * partialTrace P := by
  ext a b
  simp only [partialTrace, Matrix.mul_apply, Fintype.sum_prod_type,
    Matrix.kronecker_apply, Matrix.one_apply, Finset.mul_sum,
    mul_ite, mul_one, mul_zero, ite_mul, zero_mul]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true]
  exact Finset.sum_comm

theorem partialTrace_right (X : Matrix A A ℂ) (P : Matrix (A × B) (A × B) ℂ) :
    partialTrace (P * (X ⊗ₖ (1 : Matrix B B ℂ))) = partialTrace P * X := by
  ext a b
  simp only [partialTrace, Matrix.mul_apply, Fintype.sum_prod_type,
    Matrix.kronecker_apply, Matrix.one_apply, Finset.sum_mul,
    mul_ite, mul_one, mul_zero]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
  exact Finset.sum_comm

theorem partialTrace_environment (X : Matrix B B ℂ) (P : Matrix (A × B) (A × B) ℂ) :
    partialTrace (((1 : Matrix A A ℂ) ⊗ₖ X) * P) =
      partialTrace (P * ((1 : Matrix A A ℂ) ⊗ₖ X)) := by
  ext a b
  simp only [partialTrace, Matrix.mul_apply, Fintype.sum_prod_type,
    Matrix.kronecker_apply, Matrix.one_apply, ite_mul, one_mul, zero_mul,
    mul_ite, mul_zero, Finset.sum_ite_irrel, Finset.sum_const_zero,
    Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  exact mul_comm _ _

theorem partialTrace_add (P Q : Matrix (A × B) (A × B) ℂ) :
    partialTrace (P + Q) = partialTrace P + partialTrace Q := by
  ext a b
  simp [partialTrace, Finset.sum_add_distrib]

theorem partialTrace_commutes_of_tensor (R : Generators d A) (S : Generators d B)
    (P : Matrix (A × B) (A × B) ℂ)
    (hP : ∀ i j, (R.tensor S).E i j * P = P * (R.tensor S).E i j)
    (i j : Fin d) : partialTrace P * R.E i j = R.E i j * partialTrace P := by
  have h := congrArg partialTrace (hP i j)
  simp only [Generators.tensor, Matrix.add_mul, Matrix.mul_add,
    partialTrace_add, partialTrace_left, partialTrace_right] at h
  rw [partialTrace_environment] at h
  exact (add_right_cancel h).symm

/-- The range projection of an actual Lie intertwiner commutes with the
tensor generators by the adjoint relation. -/
theorem lie_range_commutes (R : Generators d A) (S : Generators d B) (T : Generators d C)
    (J : Matrix (A × B) C ℂ)
    (hJ : ∀ i j, (R.tensor S).E i j * J = J * T.E i j) (i j : Fin d) :
    (R.tensor S).E i j * (J * Jᴴ) = (J * Jᴴ) * (R.tensor S).E i j := by
  have ha := congrArg Matrix.conjTranspose (hJ j i)
  simp only [Matrix.conjTranspose_mul, Generators.adjoint] at ha
  rw [← Matrix.mul_assoc, hJ, Matrix.mul_assoc, ← ha, ← Matrix.mul_assoc]

/-- Genuine Lie highest cyclicity proves the exact partial-trace dimension
balance needed for the forward Cartan channel. -/
theorem balance_of_cyclic_weight [Nonempty A]
    (M : CyclicWeightModel d A) (N : CyclicWeightModel d B) (S : CyclicWeightModel d C)
    (J : Matrix (A × B) C ℂ) (hiso : Jᴴ * J = 1)
    (hJ : ∀ i j, (M.generators.tensor N.generators).E i j * J = J * S.generators.E i j) :
    partialTrace (J * Jᴴ) =
      ((Fintype.card C : ℝ) / (Fintype.card A : ℝ)) • (1 : Matrix A A ℂ) := by
  obtain ⟨c, hc⟩ := LiePBW.commutant_scalar_of_highest M.generators
    (fun i => (M.row i : ℂ)) M.highestVector M.highestVector_ne_zero
    M.vector_weight M.vector_raise M.vector_cyclic (partialTrace (J * Jᴴ))
    (partialTrace_commutes_of_tensor M.generators N.generators _
      (lie_range_commutes M.generators N.generators S.generators J hJ))
  have ht := congrArg Matrix.trace hc
  rw [trace_partialTrace, Matrix.trace_mul_comm J, hiso] at ht
  simp only [Matrix.trace_one, Matrix.trace_smul, smul_eq_mul] at ht
  have him := congrArg Complex.im ht
  simp only [Complex.natCast_im, Complex.mul_im, Complex.natCast_re,
    mul_zero, zero_add] at him
  have hd : (Fintype.card A : ℝ) ≠ 0 := by
    exact_mod_cast (Fintype.card_ne_zero : Fintype.card A ≠ 0)
  have hcim : c.im = 0 := (mul_eq_zero.mp him.symm).resolve_right hd
  have hreal : (c.re : ℂ) = c := by apply Complex.ext <;> simp [hcim]
  have hcR : partialTrace (J * Jᴴ) = c.re • (1 : Matrix A A ℂ) := by
    rw [hc, ← hreal, Complex.coe_smul]
    simp
  exact balance_of_scalar J hiso c.re hcR

end FreeEntropy.CartanBalance
