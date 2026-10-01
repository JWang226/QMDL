/-
Copyright (c) 2026 Free Entropy formalization contributors.
See LICENSE and NOTICE in the repository root for license and attribution.
-/

import FreeEntropy.CasimirWeights
import FreeEntropy.WeightSectors
import Mathlib.Data.Matrix.Basis
import Mathlib.Order.Interval.Finset.Fin
import Mathlib.Tactic.NoncommRing

/-!
# Matrix Lie generators and the quadratic Casimir

The generators satisfy the actual `gl(d)` commutator and adjoint relations.
The fundamental matrices and tensor products are constructed explicitly.
Casimir formulas below are proved by matrix multiplication and finite sums.
-/

noncomputable section
open scoped BigOperators Matrix Kronecker ComplexOrder MatrixOrder
open Matrix

namespace FreeEntropy.LieMatrixCasimir

set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

variable {d : ℕ} {H K C : Type*} [Fintype H] [Fintype K] [Fintype C]
  [DecidableEq H] [DecidableEq K] [DecidableEq C]

/-- Actual matrix generators of a unitary finite-dimensional `gl(d)` module. -/
structure Generators (d : ℕ) (H : Type*) [Fintype H] where
  E : Fin d → Fin d → Matrix H H ℂ
  adjoint : ∀ i j, (E i j)ᴴ = E j i
  commutator : ∀ i j k l,
    E i j * E k l - E k l * E i j =
      (if j = k then E i l else 0) - (if l = i then E k j else 0)

/-- The defining representation is constructed from standard matrix units. -/
def fundamental (d : ℕ) : Generators d (Fin d) where
  E i j := Matrix.single i j 1
  adjoint := by intro i j; simp
  commutator := by
    intro i j k l
    by_cases hjk : j = k <;> by_cases hli : l = i <;>
      simp [hjk, hli, Matrix.single_mul_single_of_ne]

theorem kronecker_sub_left (X Y : Matrix H H ℂ) (Z : Matrix K K ℂ) :
    (X - Y) ⊗ₖ Z = X ⊗ₖ Z - Y ⊗ₖ Z := by
  ext a b
  simp [sub_mul]

theorem kronecker_sub_right (X : Matrix H H ℂ) (Y Z : Matrix K K ℂ) :
    X ⊗ₖ (Y - Z) = X ⊗ₖ Y - X ⊗ₖ Z := by
  ext a b
  simp [mul_sub]

theorem kronecker_sum_left {ι : Type*} [Fintype ι]
    (X : ι → Matrix H H ℂ) (Y : Matrix K K ℂ) :
    (∑ i, X i) ⊗ₖ Y = ∑ i, X i ⊗ₖ Y := by
  ext a b
  simp [Matrix.sum_apply, Finset.sum_mul]

theorem kronecker_sum_right {ι : Type*} [Fintype ι]
    (X : Matrix H H ℂ) (Y : ι → Matrix K K ℂ) :
    X ⊗ₖ (∑ i, Y i) = ∑ i, X ⊗ₖ Y i := by
  ext a b
  simp [Matrix.sum_apply, Finset.mul_sum]

/-- Tensor-product Lie action. This closes the commutator and adjoint
relations for concrete tensor powers of the defining representation. -/
def Generators.tensor (R : Generators d H) (S : Generators d K) : Generators d (H × K) where
  E i j := R.E i j ⊗ₖ (1 : Matrix K K ℂ) + (1 : Matrix H H ℂ) ⊗ₖ S.E i j
  adjoint := by
    intro i j
    simp only [Matrix.conjTranspose_add, Matrix.conjTranspose_kronecker,
      Matrix.conjTranspose_one, R.adjoint, S.adjoint]
  commutator := by
    intro i j k l
    calc
      _ = (R.E i j * R.E k l - R.E k l * R.E i j) ⊗ₖ (1 : Matrix K K ℂ) +
          (1 : Matrix H H ℂ) ⊗ₖ (S.E i j * S.E k l - S.E k l * S.E i j) := by
        simp only [Matrix.add_mul, Matrix.mul_add, ← Matrix.mul_kronecker_mul,
          Matrix.one_mul, Matrix.mul_one, kronecker_sub_left, kronecker_sub_right]
        abel
      _ = _ := by
        rw [R.commutator, S.commutator]
        split_ifs <;> simp only [kronecker_sub_left, kronecker_sub_right,
          Matrix.zero_kronecker, Matrix.kronecker_zero] <;> abel

/-- The quadratic Casimir is the actual sum of matrix products. -/
def Generators.casimir (R : Generators d H) : Matrix H H ℂ :=
  ∑ i, ∑ j, R.E i j * R.E j i

theorem Generators.casimir_hermitian (R : Generators d H) : R.casimir.IsHermitian := by
  change R.casimirᴴ = R.casimir
  simp only [Generators.casimir, Matrix.conjTranspose_sum, Matrix.conjTranspose_mul, R.adjoint]

theorem Generators.casimir_positive (R : Generators d H) : R.casimir.PosSemidef := by
  apply Matrix.posSemidef_sum
  intro i _
  apply Matrix.posSemidef_sum
  intro j _
  simpa only [R.adjoint] using Matrix.posSemidef_self_mul_conjTranspose (R.E i j)

/-- Intertwining the actual Lie generators intertwines their Casimir. -/
theorem Generators.casimir_intertwines (R : Generators d H) (S : Generators d K)
    (V : Matrix H K ℂ) (hV : ∀ i j, R.E i j * V = V * S.E i j) :
    R.casimir * V = V * S.casimir := by
  simp only [Generators.casimir, Matrix.sum_mul, Matrix.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [Matrix.mul_assoc, hV j i, ← Matrix.mul_assoc, hV i j, Matrix.mul_assoc]

/-- Expanding the tensor Casimir produces its genuine exchange cross term. -/
theorem Generators.casimir_tensor (R : Generators d H) (S : Generators d K) :
    (R.tensor S).casimir =
      R.casimir ⊗ₖ (1 : Matrix K K ℂ) + (1 : Matrix H H ℂ) ⊗ₖ S.casimir +
        (2 : ℝ) • (∑ i, ∑ j, R.E i j ⊗ₖ S.E j i) := by
  have hswap : (∑ i, ∑ j, R.E j i ⊗ₖ S.E i j) = ∑ i, ∑ j, R.E i j ⊗ₖ S.E j i :=
    Finset.sum_comm
  simp only [Generators.casimir, Generators.tensor, Matrix.add_mul, Matrix.mul_add,
    ← Matrix.mul_kronecker_mul, Matrix.one_mul, Matrix.mul_one,
    Finset.sum_add_distrib, kronecker_sum_left, kronecker_sum_right]
  rw [hswap]
  module

theorem sum_positive_root_differences (lam : Fin d → ℝ) :
    (∑ i, ∑ j, if i < j then lam i - lam j else 0) =
      ∑ i, lam i * CasimirWeights.twiceRho i := by
  have hup (i : Fin d) : (∑ j, if i < j then lam i else 0) =
      ((d - 1 - i.val : ℕ) : ℝ) * lam i := by
    rw [← Finset.sum_filter]
    have he : Finset.univ.filter (fun j : Fin d => i < j) = Finset.Ioi i := by
      ext j; simp
    rw [he]
    simp
  have hlo (i : Fin d) : (∑ j, if j < i then lam i else 0) = (i.val : ℝ) * lam i := by
    rw [← Finset.sum_filter]
    have he : Finset.univ.filter (fun j : Fin d => j < i) = Finset.Iio i := by
      ext j; simp
    rw [he]
    simp
  have hsplit (i j : Fin d) : (if i < j then lam i - lam j else 0) =
      (if i < j then lam i else 0) - (if i < j then lam j else 0) := by
    split_ifs <;> simp
  simp_rw [hsplit, Finset.sum_sub_distrib]
  have hswap : (∑ i : Fin d, ∑ j : Fin d, if i < j then lam j else 0) =
      ∑ j : Fin d, ∑ i : Fin d, if i < j then lam j else 0 := Finset.sum_comm
  rw [hswap]
  simp_rw [hup, hlo]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  have hi := i.isLt
  have hcast : ((d - 1 - i.val : ℕ) : ℝ) = (d : ℝ) - 1 - (i.val : ℝ) := by
    rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]
    norm_num
  rw [hcast]
  unfold CasimirWeights.twiceRho
  ring

theorem highest_casimir_polynomial (lam : Fin d → ℝ) :
    (∑ i, lam i ^ 2) + (∑ i, ∑ j, if i < j then lam i - lam j else 0) =
      CasimirWeights.casimir lam := by
  rw [sum_positive_root_differences, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- Each summand of the Casimir on a highest-weight subspace, derived
directly from the Lie commutator and raising annihilation. -/
theorem Generators.highest_product (R : Generators d H) (P : Matrix H C ℂ)
    (lam : Fin d → ℝ) (hweight : ∀ i, R.E i i * P = lam i • P)
    (hraise : ∀ i j, i < j → R.E i j * P = 0) (i j : Fin d) :
    (R.E i j * R.E j i) * P =
      ((if i = j then lam i ^ 2 else 0) + (if i < j then lam i - lam j else 0)) • P := by
  rcases lt_trichotomy i j with hij | hij | hij
  · have hz : R.E j i * R.E i j * P = 0 := by
      rw [Matrix.mul_assoc, hraise i j hij, Matrix.mul_zero]
    have hc := congrArg (fun X : Matrix H H ℂ => X * P) (R.commutator i j j i)
    simp only [ite_true, Matrix.sub_mul, hz, sub_zero, hweight, ← sub_smul] at hc
    simpa only [if_neg hij.ne, if_pos hij, zero_add] using hc
  · subst j
    rw [Matrix.mul_assoc, hweight, Matrix.mul_smul, hweight, smul_smul]
    simp [pow_two]
  · rw [Matrix.mul_assoc, hraise j i hij, Matrix.mul_zero]
    simp [hij.ne', not_lt_of_gt hij]

/-- The actual Casimir acts on every highest-weight vector by the paper's
polynomial `c(lam) = (lam,lam+2rho)`. -/
theorem Generators.casimir_on_highest (R : Generators d H) (P : Matrix H C ℂ)
    (lam : Fin d → ℝ) (hweight : ∀ i, R.E i i * P = lam i • P)
    (hraise : ∀ i j, i < j → R.E i j * P = 0) :
    R.casimir * P = CasimirWeights.casimir lam • P := by
  simp only [Generators.casimir, Matrix.sum_mul]
  simp_rw [R.highest_product P lam hweight hraise]
  simp_rw [← Finset.sum_smul]
  congr 1
  simp only [Finset.sum_add_distrib, Finset.sum_ite_eq,
    Finset.mem_univ, ite_true]
  exact highest_casimir_polynomial lam

/-- Compression to a highest-weight subspace kills every off-diagonal
generator; lowering terms vanish by the adjoint of raising annihilation. -/
theorem Generators.highest_compression (R : Generators d H) (P : Matrix H H ℂ)
    (hP : IsStarProjection P) (lam : Fin d → ℝ)
    (hweight : ∀ i, R.E i i * P = lam i • P)
    (hraise : ∀ i j, i < j → R.E i j * P = 0) (i j : Fin d) :
    P * R.E i j * P = if i = j then lam i • P else 0 := by
  rcases lt_trichotomy i j with hij | hij | hij
  · rw [if_neg hij.ne, Matrix.mul_assoc, hraise i j hij, Matrix.mul_zero]
  · subst j
    rw [if_pos rfl, Matrix.mul_assoc, hweight, Matrix.mul_smul, hP.isIdempotentElem.eq]
  · rw [if_neg hij.ne']
    have hPH : Pᴴ = P := hP.isSelfAdjoint.star_eq
    have hzero : P * R.E i j = 0 := by
      simpa only [Matrix.conjTranspose_mul, hPH, R.adjoint,
        Matrix.conjTranspose_zero] using congrArg Matrix.conjTranspose (hraise j i hij)
    rw [hzero, Matrix.zero_mul]

/-- The actual exchange cross term compressed by a source weight space
and an auxiliary highest-weight space is its Cartan dot product. -/
theorem Generators.tensor_cross_compression (R : Generators d H) (S : Generators d K)
    (P : Matrix H H ℂ) (Q : Matrix K K ℂ) (hP : IsStarProjection P) (hQ : IsStarProjection Q)
    (lam omega : Fin d → ℝ)
    (hweightP : ∀ i, R.E i i * P = lam i • P)
    (hweightQ : ∀ i, S.E i i * Q = omega i • Q)
    (hraiseQ : ∀ i j, i < j → S.E i j * Q = 0) :
    (P ⊗ₖ Q) * (∑ i, ∑ j, R.E i j ⊗ₖ S.E j i) * (P ⊗ₖ Q) =
      CasimirWeights.dot lam omega • (P ⊗ₖ Q) := by
  simp only [Matrix.mul_sum, Matrix.sum_mul]
  have hterm (i j : Fin d) :
      (P ⊗ₖ Q) * (R.E i j ⊗ₖ S.E j i) * (P ⊗ₖ Q) =
        if i = j then (lam i * omega i) • (P ⊗ₖ Q) else 0 := by
    rw [← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul,
      S.highest_compression Q hQ omega hweightQ hraiseQ]
    by_cases hij : i = j
    · subst j
      simp only [ite_true]
      rw [Matrix.mul_assoc, hweightP, Matrix.mul_smul, hP.isIdempotentElem.eq,
        Matrix.smul_kronecker, Matrix.kronecker_smul, smul_smul]
    · simp only [if_neg hij, if_neg (Ne.symm hij), Matrix.kronecker_zero]
  simp_rw [hterm]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  rw [← Finset.sum_smul]
  rfl

/-- Casimir compression on a tensor-product weight block, including the
proved annihilation of all raising/lowering exchange terms. -/
theorem Generators.tensor_casimir_compression (R : Generators d H) (S : Generators d K)
    (P : Matrix H H ℂ) (Q : Matrix K K ℂ) (hP : IsStarProjection P) (hQ : IsStarProjection Q)
    (mu lam omega : Fin d → ℝ)
    (hcasimirP : R.casimir * P = CasimirWeights.casimir mu • P)
    (hweightP : ∀ i, R.E i i * P = lam i • P)
    (hweightQ : ∀ i, S.E i i * Q = omega i • Q)
    (hraiseQ : ∀ i j, i < j → S.E i j * Q = 0) :
    (P ⊗ₖ Q) * (R.tensor S).casimir * (P ⊗ₖ Q) =
      (CasimirWeights.casimir mu + CasimirWeights.casimir omega +
        2 * CasimirWeights.dot lam omega) • (P ⊗ₖ Q) := by
  have hpc : P * R.casimir * P = CasimirWeights.casimir mu • P := by
    rw [Matrix.mul_assoc, hcasimirP, Matrix.mul_smul, hP.isIdempotentElem.eq]
  have hqc : Q * S.casimir * Q = CasimirWeights.casimir omega • Q := by
    rw [Matrix.mul_assoc, S.casimir_on_highest Q omega hweightQ hraiseQ,
      Matrix.mul_smul, hQ.isIdempotentElem.eq]
  rw [R.casimir_tensor S]
  simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul,
    ← Matrix.mul_kronecker_mul, Matrix.mul_one]
  rw [hpc, hqc, hP.isIdempotentElem.eq, hQ.isIdempotentElem.eq,
    R.tensor_cross_compression S P Q hP hQ lam omega hweightP hweightQ hraiseQ,
    Matrix.smul_kronecker, Matrix.kronecker_smul]
  module

/-- Exact compressed deficit `2 (delta,omega)` used in the manuscript. -/
theorem Generators.tensor_casimir_deficit (R : Generators d H) (S : Generators d K)
    (P : Matrix H H ℂ) (Q : Matrix K K ℂ) (hP : IsStarProjection P) (hQ : IsStarProjection Q)
    (mu omega delta : Fin d → ℝ)
    (hcasimirP : R.casimir * P = CasimirWeights.casimir mu • P)
    (hweightP : ∀ i, R.E i i * P = (mu i - delta i) • P)
    (hweightQ : ∀ i, S.E i i * Q = omega i • Q)
    (hraiseQ : ∀ i j, i < j → S.E i j * Q = 0) :
    (P ⊗ₖ Q) * (CasimirWeights.casimir (mu + omega) • (1 : Matrix (H × K) (H × K) ℂ) -
      (R.tensor S).casimir) * (P ⊗ₖ Q) =
        (2 * CasimirWeights.dot delta omega) • (P ⊗ₖ Q) := by
  rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one,
    ← Matrix.mul_kronecker_mul, hP.isIdempotentElem.eq, hQ.isIdempotentElem.eq,
    R.tensor_casimir_compression S P Q hP hQ mu (mu - delta) omega
      hcasimirP hweightP hweightQ hraiseQ, ← sub_smul]
  congr 1
  have h := CasimirWeights.casimir_deficit mu omega delta
  linarith

end FreeEntropy.LieMatrixCasimir
