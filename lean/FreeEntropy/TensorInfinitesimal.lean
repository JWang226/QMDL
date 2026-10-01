/-
Copyright (c) 2026 Free Entropy formalization contributors.
See LICENSE and NOTICE in the repository root for license and attribution.
-/

import FreeEntropy.SchurWeylSource
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Prod

/-! The infinitesimal tensor action is constructed entry by entry and obtained
by differentiating actual tensor-power matrices. Unitary invariant subspaces
therefore also reduce this genuine infinitesimal action. -/

noncomputable section
open Matrix
open scoped BigOperators

namespace FreeEntropy.TensorPowers

variable {H : Type*} [Fintype H] [DecidableEq H]

/-- Sum of the single-site actions of `A` on all tensor factors. -/
def differential (n : ℕ) (A : Matrix H H ℂ) :
    Matrix (Fin n → H) (Fin n → H) ℂ := fun x y =>
  ∑ t : Fin n, (∏ s ∈ Finset.univ.erase t, (1 : Matrix H H ℂ) (x s) (y s)) * A (x t) (y t)

theorem differential_add (n : ℕ) (A B : Matrix H H ℂ) :
    differential n (A + B) = differential n A + differential n B := by
  ext x y
  simp [differential, mul_add, Finset.sum_add_distrib]

theorem differential_smul (n : ℕ) (c : ℂ) (A : Matrix H H ℂ) :
    differential n (c • A) = c • differential n A := by
  ext x y
  simp [differential, Finset.mul_sum, mul_left_comm]

theorem differential_sub (n : ℕ) (A B : Matrix H H ℂ) :
    differential n (A - B) = differential n A - differential n B := by
  ext x y
  simp [differential, mul_sub, Finset.sum_sub_distrib]

/-- The explicit tensor Lie action is the derivative of the actual tensor
polynomial at the identity, over real scalar parameters. -/
theorem hasDerivAt_matrix_identity (n : ℕ) (A : Matrix H H ℂ)
    (x y : Fin n → H) :
    HasDerivAt (fun t : ℝ => TensorPowers.matrix n ((1 : Matrix _ _ ℂ) + t • A) x y) (differential n A x y) 0 := by
  have hf (s : Fin n) : HasDerivAt
      (fun t : ℝ => (1 : Matrix H H ℂ) (x s) (y s) + t • A (x s) (y s))
      (A (x s) (y s)) 0 := by
    simpa only [Pi.add_apply, zero_add, one_smul] using (hasDerivAt_const (0 : ℝ) ((1 : Matrix H H ℂ) (x s) (y s))).add
      ((hasDerivAt_id (0 : ℝ)).smul_const (A (x s) (y s)))
  simpa [matrix, differential, smul_eq_mul] using
    HasDerivAt.fun_finset_prod (u := Finset.univ) (fun s _ => hf s)

end FreeEntropy.TensorPowers

namespace FreeEntropy.SchurWeyl
open TensorPowers
variable {d n : ℕ}

/-- Differentiating the already proved mixed-source commutation identity
shows that the true unitary commutant commutes with every Hermitian Lie action. -/
theorem TensorCommutant.differential_hermitian
    {T : Matrix (Fin n → Fin d) (Fin n → Fin d) ℂ} (hT : TensorCommutant T)
    {A : Matrix (Fin d) (Fin d) ℂ} (hA : A.IsHermitian) :
    T * differential n A = differential n A * T := by
  ext x y
  have hL : HasDerivAt (fun t : ℝ => (T * TensorPowers.matrix n ((1 : Matrix (Fin d) (Fin d) ℂ) + t • A)) x y)
      ((T * differential n A) x y) 0 := by
    simpa only [Matrix.mul_apply, Finset.sum_apply] using
      HasDerivAt.fun_sum (u := Finset.univ) (fun z _ =>
        (hasDerivAt_matrix_identity n A z y).const_mul (T x z))
  have hR : HasDerivAt (fun t : ℝ => (TensorPowers.matrix n ((1 : Matrix (Fin d) (Fin d) ℂ) + t • A) * T) x y)
      ((differential n A * T) x y) 0 := by
    simpa only [Matrix.mul_apply, Finset.sum_apply] using
      HasDerivAt.fun_sum (u := Finset.univ) (fun z _ =>
        (hasDerivAt_matrix_identity n A x z).mul_const (T z y))
  have he : (fun t : ℝ => (T * TensorPowers.matrix n ((1 : Matrix (Fin d) (Fin d) ℂ) + t • A)) x y) =
      (fun t : ℝ => (TensorPowers.matrix n ((1 : Matrix (Fin d) (Fin d) ℂ) + t • A) * T) x y) := by
    funext t
    have hh : (1 + t • A).IsHermitian := by
      change (1 + t • A)ᴴ = 1 + t • A
      simp [Matrix.conjTranspose_smul, hA.eq]
    exact congrArg (fun M => M x y) (hT.hermitian hh)
  rw [he] at hL
  exact hL.unique hR

/-- Complex linearity extends the differentiation argument to all matrix
directions, including the individual raising and lowering matrix units. -/
theorem TensorCommutant.differential
    {T : Matrix (Fin n → Fin d) (Fin n → Fin d) ℂ} (hT : TensorCommutant T)
    (A : Matrix (Fin d) (Fin d) ℂ) :
    T * TensorPowers.differential n A = TensorPowers.differential n A * T := by
  let B : Matrix (Fin d) (Fin d) ℂ := (1 / 2 : ℂ) • (A + Aᴴ)
  let C : Matrix (Fin d) (Fin d) ℂ := (Complex.I / 2) • (Aᴴ - A)
  have hB : B.IsHermitian := by
    change Bᴴ = B
    simp [B, Matrix.conjTranspose_smul, add_comm]
  have hC : C.IsHermitian := by
    change Cᴴ = C
    simp only [C, Matrix.conjTranspose_smul, Matrix.conjTranspose_sub,
      Matrix.conjTranspose_conjTranspose, star_div₀, star_ofNat, Complex.star_def,
      map_div₀, Complex.conj_I, map_ofNat]
    ext i j
    simp only [Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul]
    ring
  have hA : A = B + Complex.I • C := by
    ext i j
    simp only [B, C, Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
    linear_combination -(Aᴴ i j - A i j) / 2 * Complex.I_sq
  rw [hA, differential_add, differential_smul n Complex.I C, Matrix.mul_add, Matrix.add_mul,
    Matrix.mul_smul, Matrix.smul_mul, hT.differential_hermitian hB,
    hT.differential_hermitian hC]

end FreeEntropy.SchurWeyl
