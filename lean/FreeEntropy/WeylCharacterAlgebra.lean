/-
Copyright (c) 2026 Free Entropy formalization contributors.
See LICENSE and NOTICE in the repository root for license and attribution.
-/

import FreeEntropy.CasimirDecomposition
import Mathlib.Algebra.MvPolynomial.PDeriv

/-! Finite polynomial and Casimir identities for deriving an actual Weyl
character formula: Euler derivatives act diagonally on monomial exponents,
and shifted quadratic energy separates dominant weights in one root cone. -/
noncomputable section
open scoped BigOperators
namespace FreeEntropy.WeylCharacter
open MvPolynomial CasimirWeights
set_option backward.isDefEq.respectTransparency false
variable {d : ℕ}

/-- The actual formal Euler derivative in one coordinate. -/
def euler (i : Fin d) : MvPolynomial (Fin d) ℂ →ₗ[ℂ] MvPolynomial (Fin d) ℂ where
  toFun p := X i * pderiv i p
  map_add' p q := by simp [mul_add]
  map_smul' c p := by simp [mul_smul_comm]

theorem euler_monomial (i : Fin d) (m : Fin d →₀ ℕ) (c : ℂ) :
    euler i (monomial m c) = (m i : ℂ) • monomial m c := by
  change X i * pderiv i (monomial m c) = _
  rw [X_mul_pderiv_monomial]
  simp only [Nat.cast_smul_eq_nsmul]

theorem coeff_euler (i : Fin d) (p : MvPolynomial (Fin d) ℂ) (m : Fin d →₀ ℕ) :
    coeff m (euler i p) = (m i : ℂ) * coeff m p := by
  classical
  induction p using MvPolynomial.induction_on' with
  | add p q hp hq => simp only [map_add, coeff_add, hp, hq, mul_add]
  | monomial a c =>
    rw [euler_monomial]
    by_cases ha : a = m
    · subst a; simp
    · simp [coeff_monomial, ha, Ne.symm ha]

/-- The flat torus Laplacian, as a genuine formal differential operator. -/
def laplacian : MvPolynomial (Fin d) ℂ →ₗ[ℂ] MvPolynomial (Fin d) ℂ :=
  ∑ i : Fin d, (euler i).comp (euler i)

def exponentEnergy (m : Fin d →₀ ℕ) : ℕ := ∑ i : Fin d, m i ^ 2

theorem coeff_laplacian (p : MvPolynomial (Fin d) ℂ) (m : Fin d →₀ ℕ) :
    coeff m (laplacian p) = (exponentEnergy m : ℂ) * coeff m p := by
  simp only [laplacian, LinearMap.sum_apply, LinearMap.comp_apply,
    exponentEnergy, Nat.cast_sum, Nat.cast_pow, Finset.sum_mul]
  rw [MvPolynomial.coeff_sum]
  simp only [coeff_euler]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- Every nonzero coefficient of a Laplacian eigenpolynomial has the
prescribed squared exponent norm. -/
theorem eigenpolynomial_support_energy (p : MvPolynomial (Fin d) ℂ) (E : ℕ)
    (hp : laplacian p = (E : ℂ) • p) (m : Fin d →₀ ℕ) (hm : coeff m p ≠ 0) :
    exponentEnergy m = E := by
  have h := congrArg (coeff m) hp
  rw [coeff_laplacian, coeff_smul] at h
  exact_mod_cast mul_right_cancel₀ hm h

/-- Positive-root offsets preserve the total coordinate sum. -/
theorem sum_offset_zero (c : Fin (d - 1) → ℕ) : ∑ i : Fin d, offset c i = 0 := by
  simp only [offset]
  rw [Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro j _
  rw [← Finset.mul_sum]
  simp [simpleRoot, Finset.sum_sub_distrib]

/-- A dominant point has a strictly smaller Casimir than any different
dominant point above it by an integral positive-root offset. -/
theorem dominant_casimir_unique (nu chi : Fin d → ℝ) (c : Fin (d - 1) → ℕ)
    (hnu : ∀ j, nu (right j) ≤ nu (left j))
    (hchi : ∀ j, chi (right j) ≤ chi (left j))
    (hc : nu - chi = offset c) (he : casimir nu = casimir chi) : chi = nu := by
  have hz : c = 0 := by
    by_contra hn
    have hex : ∃ j, c j ≠ 0 := by
      by_contra h
      push_neg at h
      exact hn (funext h)
    have hgap := casimir_gap nu chi c 0 le_rfl hex hc
      (fun j _ => sub_nonneg.mpr (hnu j)) hchi
    rw [he, sub_self] at hgap
    linarith
  have hzero : nu - chi = 0 := by
    rw [hc, hz]
    funext i
    simp [offset]
  exact (sub_eq_zero.mp hzero).symm

/-- Integer staircase used in the polynomial Weyl denominator. -/
def staircase (i : Fin d) : ℝ := (d : ℝ) - 1 - (i.val : ℝ)

def shiftedEnergy (x : Fin d → ℝ) : ℝ := ∑ i, (x i + staircase i) ^ 2

theorem shiftedEnergy_eq (x : Fin d → ℝ) :
    shiftedEnergy x = casimir x + ((d : ℝ) - 1) * (∑ i, x i) +
      ∑ i : Fin d, staircase i ^ 2 := by
  simp only [shiftedEnergy, casimir, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  simp only [staircase, twiceRho]
  ring

/-- The shifted-energy step that eliminates all lower dominant exponents
from an alternating character eigenpolynomial. -/
theorem dominant_shiftedEnergy_unique (nu chi : Fin d → ℝ) (c : Fin (d - 1) → ℕ)
    (hnu : ∀ j, nu (right j) ≤ nu (left j))
    (hchi : ∀ j, chi (right j) ≤ chi (left j))
    (hc : nu - chi = offset c) (he : shiftedEnergy nu = shiftedEnergy chi) : chi = nu := by
  have hs := congrArg (fun x : Fin d → ℝ => ∑ i, x i) hc
  simp only [Pi.sub_apply, Finset.sum_sub_distrib, sum_offset_zero] at hs
  rw [shiftedEnergy_eq, shiftedEnergy_eq, sub_eq_zero.mp hs] at he
  apply dominant_casimir_unique nu chi c hnu hchi hc
  linarith

end FreeEntropy.WeylCharacter
