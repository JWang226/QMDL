/-
Copyright (c) 2026 Free Entropy formalization contributors.
See LICENSE and NOTICE in the repository root for license and attribution.
-/

import FreeEntropy.LieDepthMultiplicity
import FreeEntropy.WeightNormalization

/-! Concrete normalized diagonal states of actual cyclic highest-weight
models. Relative eigenvalues are the actual simple-root ratio monomials;
finite block normalization and the common coefficient ratio are derived. -/
noncomputable section
open Matrix
open scoped BigOperators
namespace FreeEntropy.CartanLieCloning
open CasimirWeights WeightSectors WeightNormalization CloningMatrices
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
variable {d : ℕ} {A : Type*} [Fintype A] [DecidableEq A]

def rootWeightMonomial (ratio : Fin (d - 1) → ℝ) (delta : Fin (d - 1) → ℕ) : ℝ :=
  ∏ j, ratio j ^ delta j

def CyclicWeightModel.relativeWeight (M : CyclicWeightModel d A)
    (ratio : Fin (d - 1) → ℝ) (a : A) : ℝ :=
  rootWeightMonomial ratio (M.weightCoeff a)

def CyclicWeightModel.relativeNormalizer (M : CyclicWeightModel d A)
    (ratio : Fin (d - 1) → ℝ) : ℝ := ∑ a, M.relativeWeight ratio a

def CyclicWeightModel.relativeState (M : CyclicWeightModel d A)
    (ratio : Fin (d - 1) → ℝ) : Matrix A A ℂ :=
  Matrix.diagonal (fun a => ((M.relativeWeight ratio a / M.relativeNormalizer ratio : ℝ) : ℂ))

def CyclicWeightModel.offsetSupport (M : CyclicWeightModel d A) : Finset (Fin (d - 1) → ℕ) := by
  classical
  exact Finset.univ.image M.weightCoeff

def CyclicWeightModel.offsetMultiplicity (M : CyclicWeightModel d A)
    (delta : Fin (d - 1) → ℕ) : ℕ := weightMultiplicity M.weight (M.row - offset delta)

def CyclicWeightModel.offsetCoefficient (M : CyclicWeightModel d A)
    (s : Finset (Fin (d - 1) → ℕ)) (ratio : Fin (d - 1) → ℝ)
    (delta : Fin (d - 1) → ℕ) : ℝ :=
  coefficient s M.offsetMultiplicity (rootWeightMonomial ratio) delta

@[simp] theorem rootWeightMonomial_zero (ratio : Fin (d - 1) → ℝ) :
    rootWeightMonomial ratio 0 = 1 := by simp [rootWeightMonomial]

theorem rootWeightMonomial_nonneg (ratio : Fin (d - 1) → ℝ) (hratio : ∀ j, 0 ≤ ratio j)
    (delta : Fin (d - 1) → ℕ) : 0 ≤ rootWeightMonomial ratio delta :=
  Finset.prod_nonneg (fun j _ => pow_nonneg (hratio j) _)

theorem rootWeightMonomial_envelope (ratio : Fin (d - 1) → ℝ) (q : ℝ)
    (hratio : ∀ j, 0 ≤ ratio j) (hbound : ∀ j, ratio j ≤ q) (delta : Fin (d - 1) → ℕ) :
    rootWeightMonomial ratio delta ≤ q ^ depth delta := by
  exact MeanDepth.root_monomial_le Finset.univ delta ratio q (fun j _ => hratio j) (fun j _ => hbound j)

theorem CyclicWeightModel.relativeWeight_nonneg (M : CyclicWeightModel d A)
    (ratio : Fin (d - 1) → ℝ) (hratio : ∀ j, 0 ≤ ratio j) (a : A) :
    0 ≤ M.relativeWeight ratio a := rootWeightMonomial_nonneg ratio hratio _

theorem CyclicWeightModel.relativeWeight_envelope (M : CyclicWeightModel d A)
    (ratio : Fin (d - 1) → ℝ) (q : ℝ) (hratio : ∀ j, 0 ≤ ratio j) (hbound : ∀ j, ratio j ≤ q) (a : A) :
    M.relativeWeight ratio a ≤ q ^ M.basisDepth a := rootWeightMonomial_envelope ratio q hratio hbound _

theorem CyclicWeightModel.weightCoeff_highest [Nonempty A] (M : CyclicWeightModel d A) :
    M.weightCoeff M.highestBasis = 0 := by
  apply M.weightCoeff_eq_of_weight
  have hz : offset (0 : Fin (d - 1) → ℕ) = 0 := by funext k; simp [offset]
  rw [hz, sub_zero]
  exact M.highestBasis_weight

theorem CyclicWeightModel.basisDepth_eq_zero_iff [Nonempty A] (M : CyclicWeightModel d A) (a : A) :
    M.basisDepth a = 0 ↔ a = M.highestBasis := by
  constructor
  · intro h
    have hc : M.weightCoeff a = 0 := by
      funext j
      have hj := Finset.single_le_sum (s := Finset.univ) (f := M.weightCoeff a)
        (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
      change M.weightCoeff a j ≤ M.basisDepth a at hj
      rw [h] at hj
      exact Nat.eq_zero_of_le_zero hj
    have hw : M.weight a = M.row := by
      have he := M.weight_cone a
      rw [hc] at he
      have hz : offset (0 : Fin (d - 1) → ℕ) = 0 := by funext k; simp [offset]
      have he' : M.row - M.weight a = 0 := by simpa only [hz] using he
      exact (sub_eq_zero.mp he').symm
    exact M.highest_basis_unique a M.highestBasis hw M.highestBasis_weight
  · rintro rfl
    simp [basisDepth, M.weightCoeff_highest, depth]

@[simp] theorem CyclicWeightModel.relativeWeight_highest [Nonempty A]
    (M : CyclicWeightModel d A) (ratio : Fin (d - 1) → ℝ) :
    M.relativeWeight ratio M.highestBasis = 1 := by
  simp [relativeWeight, M.weightCoeff_highest]

theorem CyclicWeightModel.relativeNormalizer_ge_one [Nonempty A]
    (M : CyclicWeightModel d A) (ratio : Fin (d - 1) → ℝ) (hratio : ∀ j, 0 ≤ ratio j) :
    1 ≤ M.relativeNormalizer ratio := by
  have h := Finset.single_le_sum (s := Finset.univ) (f := M.relativeWeight ratio)
    (fun a _ => M.relativeWeight_nonneg ratio hratio a) (Finset.mem_univ M.highestBasis)
  simpa only [M.relativeWeight_highest] using h

end FreeEntropy.CartanLieCloning
