/-
Copyright (c) 2026 Free Entropy formalization contributors.
See LICENSE and NOTICE in the repository root for license and attribution.
-/

import FreeEntropy.CartanLieCloning
import FreeEntropy.WeylCharacterAlgebra
import Mathlib.Algebra.MvPolynomial.PDeriv

/-! The radial Casimir character equation is derived directly from actual
matrix commutators and traces, with literal natural weight exponents. -/
noncomputable section
open Matrix
open scoped BigOperators
namespace FreeEntropy.LieCharacter
open LieMatrixCasimir
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
variable {d : ℕ} {H : Type*} [Fintype H] [DecidableEq H]
abbrev Poly (d : ℕ) := MvPolynomial (Fin d) ℂ

def exponent (w : Fin d → ℕ) : Fin d →₀ ℕ := Finsupp.equivFunOnFinite.symm w

def weightMonomial (w : Fin d → ℕ) : Poly d := MvPolynomial.monomial (exponent w) 1

def character (weight : H → Fin d → ℕ) : Poly d := ∑ h, weightMonomial (weight h)

def weightMatrix (weight : H → Fin d → ℕ) : Matrix H H (Poly d) :=
  diagonal (fun h => weightMonomial (weight h))

def lift (M : Matrix H H ℂ) : Matrix H H (Poly d) := MvPolynomial.C.mapMatrix M

@[simp] theorem lift_mul (M N : Matrix H H ℂ) :
    lift (d := d) (M * N) = lift M * lift N := map_mul MvPolynomial.C.mapMatrix M N

@[simp] theorem lift_sub (M N : Matrix H H ℂ) :
    lift (d := d) (M - N) = lift M - lift N := map_sub MvPolynomial.C.mapMatrix M N

@[simp] theorem lift_one : lift (d := d) (1 : Matrix H H ℂ) = 1 := map_one MvPolynomial.C.mapMatrix

@[simp] theorem trace_weightMatrix (weight : H → Fin d → ℕ) :
    (weightMatrix weight).trace = character weight := Matrix.trace_diagonal _

/-- The root shift expressed without any truncated natural subtraction. -/
theorem generator_exponent_shift (R : Generators d H) (weight : H → Fin d → ℕ)
    (hdiag : ∀ k, R.E k k = diagonal (fun h => (weight h k : ℂ)))
    (i j : Fin d) (hij : i ≠ j) (a b : H) (hab : R.E i j a b ≠ 0) :
    Finsupp.single j 1 + exponent (weight a) = Finsupp.single i 1 + exponent (weight b) := by
  have hw := CartanLieCloning.generator_weight_shift R (fun a k => (weight a k : ℝ))
    (fun k => by simpa only [WeightSectors.weightDiagonal, Complex.ofReal_natCast] using hdiag k)
    i j hij a b hab
  ext k
  have hh := hw k
  simp only [Finsupp.add_apply, Finsupp.single_apply, exponent,
    Finsupp.coe_equivFunOnFinite_symm]
  by_cases hki : k = i <;> by_cases hkj : k = j
  · exact (hij (hki.symm.trans hkj)).elim
  · subst k
    simp only [ite_true, if_neg hij, if_neg (Ne.symm hij), zero_add] at hh ⊢
    exact_mod_cast (show (weight a i : ℝ) = 1 + weight b i by linarith)
  · subst k
    simp only [ite_true, if_neg hij, if_neg (Ne.symm hij), zero_add] at hh ⊢
    exact_mod_cast (show 1 + (weight a j : ℝ) = weight b j by linarith)
  · simp only [if_neg hki, if_neg hkj, if_neg (Ne.symm hki), if_neg (Ne.symm hkj),
      zero_add] at hh ⊢
    exact_mod_cast (show (weight a k : ℝ) = weight b k by linarith)

theorem variable_weight_intertwines (R : Generators d H) (weight : H → Fin d → ℕ)
    (hdiag : ∀ k, R.E k k = diagonal (fun h => (weight h k : ℂ)))
    (i j : Fin d) (hij : i ≠ j) :
    (MvPolynomial.X j : Poly d) • (weightMatrix weight * lift (R.E i j)) =
      (MvPolynomial.X i : Poly d) • (lift (R.E i j) * weightMatrix weight) := by
  apply Matrix.ext
  intro a b
  simp only [Matrix.smul_apply, Matrix.diagonal_mul, Matrix.mul_diagonal, weightMatrix,
    smul_eq_mul]
  by_cases hab : R.E i j a b = 0
  · simp [lift, hab]
  · have hm : MvPolynomial.X j * weightMonomial (weight a) =
        MvPolynomial.X i * weightMonomial (weight b) := by
      simp only [MvPolynomial.X, weightMonomial, MvPolynomial.monomial_mul, one_mul]
      rw [generator_exponent_shift R weight hdiag i j hij a b hab]
    change MvPolynomial.X j * (weightMonomial (weight a) * _) =
      MvPolynomial.X i * (_ * weightMonomial (weight b))
    rw [← mul_assoc, hm]
    ring

/-- The first Euler moment of the literal character. -/
def moment (weight : H → Fin d → ℕ) (i : Fin d) : Poly d :=
  ∑ h, MvPolynomial.C (weight h i : ℂ) * weightMonomial (weight h)

def pairTrace (R : Generators d H) (weight : H → Fin d → ℕ) (i j : Fin d) : Poly d :=
  (weightMatrix weight * lift (R.E i j) * lift (R.E j i)).trace

theorem diagonal_trace (R : Generators d H) (weight : H → Fin d → ℕ)
    (hdiag : ∀ k, R.E k k = diagonal (fun h => (weight h k : ℂ))) (i : Fin d) :
    (weightMatrix weight * lift (R.E i i)).trace = moment weight i := by
  rw [hdiag]
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.diagonal_mul, weightMatrix,
    lift, RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.diagonal_apply_eq, moment]
  apply Finset.sum_congr rfl
  intro h _
  exact mul_comm _ _

/-- Cyclicity of trace converts the actual root-shift intertwiner into the
radial relation for opposite raising/lowering products. -/
theorem variable_pairTrace (R : Generators d H) (weight : H → Fin d → ℕ)
    (hdiag : ∀ k, R.E k k = diagonal (fun h => (weight h k : ℂ)))
    (i j : Fin d) (hij : i ≠ j) :
    MvPolynomial.X j * pairTrace R weight i j =
      MvPolynomial.X i * pairTrace R weight j i := by
  have he := congrArg (fun A => (A * lift (R.E j i)).trace)
    (variable_weight_intertwines R weight hdiag i j hij)
  simp only [Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul] at he
  change _ = MvPolynomial.X i * (lift (R.E i j) * weightMatrix weight * lift (R.E j i)).trace at he
  have hcycle : (lift (R.E i j) * weightMatrix weight * lift (R.E j i)).trace =
      (weightMatrix weight * lift (R.E j i) * lift (R.E i j)).trace := by
    rw [Matrix.trace_mul_cycle, Matrix.trace_mul_cycle]
  rw [hcycle] at he
  exact he

/-- The opposite-product difference is exactly the difference of first
weight moments, as forced by the actual gl(d) commutator. -/
theorem pairTrace_sub (R : Generators d H) (weight : H → Fin d → ℕ)
    (hdiag : ∀ k, R.E k k = diagonal (fun h => (weight h k : ℂ)))
    (i j : Fin d) :
    pairTrace R weight i j - pairTrace R weight j i = moment weight i - moment weight j := by
  have he := congrArg (fun A => (weightMatrix weight * lift A).trace) (R.commutator i j j i)
  simp only [ite_true, lift_sub, lift_mul, Matrix.mul_sub, Matrix.trace_sub,
    ← Matrix.mul_assoc, diagonal_trace R weight hdiag] at he
  exact he

/-- Polynomial radial identity, valid even when coordinates coincide:
no division by a root or regularity assumption is used. -/
theorem root_radial_identity (R : Generators d H) (weight : H → Fin d → ℕ)
    (hdiag : ∀ k, R.E k k = diagonal (fun h => (weight h k : ℂ)))
    (i j : Fin d) (hij : i ≠ j) :
    (MvPolynomial.X i - MvPolynomial.X j) *
        (pairTrace R weight i j + pairTrace R weight j i) =
      (MvPolynomial.X i + MvPolynomial.X j) * (moment weight i - moment weight j) := by
  have hq := variable_pairTrace R weight hdiag i j hij
  have hc := pairTrace_sub R weight hdiag i j
  linear_combination -2 * hq + (MvPolynomial.X i + MvPolynomial.X j) * hc

/-- First moments are actual formal Euler derivatives. -/
theorem euler_character (weight : H → Fin d → ℕ) (i : Fin d) :
    WeylCharacter.euler i (character weight) = moment weight i := by
  simp only [character, map_sum, weightMonomial, WeylCharacter.euler_monomial, moment]
  apply Finset.sum_congr rfl
  intro h _
  simp only [exponent, Finsupp.coe_equivFunOnFinite_symm, Algebra.smul_def,
    MvPolynomial.algebraMap_eq]

def secondMoment (weight : H → Fin d → ℕ) (i : Fin d) : Poly d :=
  ∑ h, MvPolynomial.C ((weight h i : ℂ) ^ 2) * weightMonomial (weight h)

theorem euler_sq_character (weight : H → Fin d → ℕ) (i : Fin d) :
    WeylCharacter.euler i (WeylCharacter.euler i (character weight)) = secondMoment weight i := by
  simp only [character, map_sum, weightMonomial, WeylCharacter.euler_monomial,
    map_smul, smul_smul, secondMoment]
  apply Finset.sum_congr rfl
  intro h _
  simp only [exponent, Finsupp.coe_equivFunOnFinite_symm, Algebra.smul_def,
    MvPolynomial.algebraMap_eq, pow_two]

theorem pairTrace_diagonal (R : Generators d H) (weight : H → Fin d → ℕ)
    (hdiag : ∀ k, R.E k k = diagonal (fun h => (weight h k : ℂ))) (i : Fin d) :
    pairTrace R weight i i = secondMoment weight i := by
  rw [pairTrace, hdiag]
  simp only [lift, RingHom.mapMatrix_apply, Matrix.diagonal_map (map_zero _),
    Matrix.diagonal_mul_diagonal, weightMatrix, Matrix.trace_diagonal, secondMoment]
  apply Finset.sum_congr rfl
  intro h _
  simp only [Pi.mul_apply, map_pow]
  ring

/-- Split an arbitrary finite double sum into diagonal and opposite pairs. -/
theorem sum_diagonal_upper (f : Fin d → Fin d → Poly d) :
    (∑ i, ∑ j, f i j) = (∑ i, f i i) +
      ∑ i, ∑ j, if i < j then f i j + f j i else 0 := by
  have hs (i j : Fin d) : f i j =
      (if i = j then f i j else 0) + (if i < j then f i j else 0) +
      (if j < i then f i j else 0) := by
    rcases lt_trichotomy i j with h | h | h
    · simp [h, h.ne, not_lt_of_gt h]
    · subst j; simp
    · simp [h, h.ne', not_lt_of_gt h]
  have he : (∑ i, ∑ j, f i j) =
      (∑ i, f i i) + (∑ i, ∑ j, if i < j then f i j else 0) +
      (∑ i, ∑ j, if j < i then f i j else 0) := by
    calc
      _ = ∑ i, ∑ j, ((if i = j then f i j else 0) +
          (if i < j then f i j else 0) + (if j < i then f i j else 0)) := by
        apply Finset.sum_congr rfl
        intro i _
        exact Finset.sum_congr rfl (fun j _ => hs i j)
      _ = _ := by simp only [Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rw [he]
  have hswap : (∑ i : Fin d, ∑ j : Fin d, if j < i then f i j else 0) =
      ∑ i : Fin d, ∑ j : Fin d, if i < j then f j i else 0 := Finset.sum_comm
  rw [hswap]
  have hp (i j : Fin d) : (if i < j then f i j + f j i else 0) =
      (if i < j then f i j else 0) + (if i < j then f j i else 0) := by
    split_ifs <;> simp
  simp_rw [hp, Finset.sum_add_distrib]
  abel

/-- The complete trace Casimir equation before eliminating opposite-root
products. Its scalar premise is proved for every actual highest cyclic model. -/
theorem casimir_trace_identity (R : Generators d H) (weight : H → Fin d → ℕ)
    (hdiag : ∀ k, R.E k k = diagonal (fun h => (weight h k : ℂ)))
    (c : ℂ) (hc : R.casimir = c • (1 : Matrix H H ℂ)) :
    MvPolynomial.C c * character weight = WeylCharacter.laplacian (character weight) +
      ∑ i, ∑ j, if i < j then pairTrace R weight i j + pairTrace R weight j i else 0 := by
  have ht : (weightMatrix weight * lift R.casimir).trace =
      ∑ i, ∑ j, pairTrace R weight i j := by
    simp only [Generators.casimir, lift, map_sum, map_mul, Matrix.mul_sum,
      Matrix.trace_sum, pairTrace, Matrix.mul_assoc]
  have ht' : (weightMatrix weight * lift R.casimir).trace = MvPolynomial.C c * character weight := by
    rw [hc]
    have hl : lift (d := d) (c • (1 : Matrix H H ℂ)) = (MvPolynomial.C c : Poly d) • 1 := by
      apply Matrix.ext
      intro a b
      by_cases hab : a = b <;> simp [lift, Matrix.one_apply, hab]
    rw [hl, Matrix.mul_smul, Matrix.mul_one, Matrix.trace_smul, trace_weightMatrix, smul_eq_mul]
  rw [ht', sum_diagonal_upper] at ht
  rw [ht]
  congr 1
  simp only [WeylCharacter.laplacian, LinearMap.sum_apply, LinearMap.comp_apply,
    euler_sq_character, pairTrace_diagonal R weight hdiag]

/-- Actual finite positive-root index set. -/
def positiveRoots (d : ℕ) : Finset (Fin d × Fin d) := Finset.univ.filter (fun p => p.1 < p.2)

def rootFactor (p : Fin d × Fin d) : Poly d := MvPolynomial.X p.2 - MvPolynomial.X p.1

def rootProduct (d : ℕ) : Poly d := ∏ p ∈ positiveRoots d, rootFactor p

def rootProductExcept (p : Fin d × Fin d) : Poly d :=
  ∏ q ∈ (positiveRoots d).erase p, rootFactor q

theorem rootProduct_factor (p : Fin d × Fin d) (hp : p ∈ positiveRoots d) :
    rootProduct d = rootFactor p * rootProductExcept p := by
  exact (Finset.mul_prod_erase _ _ hp).symm

theorem sum_positiveRoots (f : Fin d × Fin d → Poly d) :
    (∑ p ∈ positiveRoots d, f p) = ∑ i, ∑ j, if i < j then f (i, j) else 0 := by
  simp only [positiveRoots, Finset.sum_filter, Fintype.sum_prod_type]

/-- A denominator-cleared radial Casimir equation derived entirely from
actual generators, actual diagonal weights, and their scalar Casimir. -/
theorem radial_casimir_identity (R : Generators d H) (weight : H → Fin d → ℕ)
    (hdiag : ∀ k, R.E k k = diagonal (fun h => (weight h k : ℂ)))
    (c : ℂ) (hc : R.casimir = c • (1 : Matrix H H ℂ)) :
    rootProduct d * (MvPolynomial.C c * character weight - WeylCharacter.laplacian (character weight)) =
      ∑ p ∈ positiveRoots d, rootProductExcept p *
        (MvPolynomial.X p.1 + MvPolynomial.X p.2) *
        (WeylCharacter.euler p.2 (character weight) - WeylCharacter.euler p.1 (character weight)) := by
  have ht := casimir_trace_identity R weight hdiag c hc
  rw [← sum_positiveRoots (fun p => pairTrace R weight p.1 p.2 + pairTrace R weight p.2 p.1)] at ht
  rw [ht, add_sub_cancel_left, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p hp
  have hij : p.1 < p.2 := (Finset.mem_filter.mp hp).2
  have hr := root_radial_identity R weight hdiag p.1 p.2 (ne_of_lt hij)
  rw [rootProduct_factor p hp, rootFactor, euler_character, euler_character]
  linear_combination -(rootProductExcept p) * hr

/-- On an actual cyclic weight model the Casimir scalar is proved, so the
radial equation needs only the literal natural labels of its weight basis. -/
theorem cyclic_radial_identity (M : CartanLieCloning.CyclicWeightModel d H)
    (weight : H → Fin d → ℕ) (hw : ∀ h i, M.weight h i = (weight h i : ℝ)) :
    rootProduct d * (MvPolynomial.C (CasimirWeights.casimir M.row : ℂ) * character weight -
        WeylCharacter.laplacian (character weight)) =
      ∑ p ∈ positiveRoots d, rootProductExcept p *
        (MvPolynomial.X p.1 + MvPolynomial.X p.2) *
        (WeylCharacter.euler p.2 (character weight) - WeylCharacter.euler p.1 (character weight)) := by
  apply radial_casimir_identity M.generators weight
  · intro k
    rw [M.diagonal]
    simp only [WeightSectors.weightDiagonal, hw, Complex.ofReal_natCast]
  · simpa only [Complex.coe_smul] using M.casimir_scalar

end FreeEntropy.LieCharacter
