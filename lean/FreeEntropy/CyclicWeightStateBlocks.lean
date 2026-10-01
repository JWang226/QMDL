/-
Copyright (c) 2026 Free Entropy formalization contributors.
See LICENSE and NOTICE in the repository root for license and attribution.
-/

import FreeEntropy.CyclicWeightStates
import FreeEntropy.CartanMultiplicity

/-! Finite weight-projector decompositions of the concrete normalized states.
All coefficients, their normalization, and their shared scalar ratio are
actual finite formulas, not spectral hypotheses. -/
noncomputable section
open Matrix
open scoped BigOperators
namespace FreeEntropy.CartanLieCloning
open CasimirWeights WeightSectors WeightNormalization CloningMatrices
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
variable {d : ℕ} {A : Type*} [Fintype A] [DecidableEq A]

theorem CyclicWeightModel.weight_iff_weightCoeff (M : CyclicWeightModel d A)
    (a : A) (delta : Fin (d - 1) → ℕ) :
    M.weight a = M.row - offset delta ↔ M.weightCoeff a = delta := by
  constructor
  · exact M.weightCoeff_eq_of_weight a delta
  · intro hc
    have h := M.weight_cone a
    rw [hc] at h
    funext k
    have hk := congrFun h k
    dsimp at hk ⊢
    linarith

theorem CyclicWeightModel.offsetMultiplicity_eq_card (M : CyclicWeightModel d A)
    (delta : Fin (d - 1) → ℕ) :
    M.offsetMultiplicity delta = (Finset.univ.filter (fun a => M.weightCoeff a = delta)).card := by
  classical
  unfold offsetMultiplicity weightMultiplicity
  congr 1
  ext a
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, M.weight_iff_weightCoeff]

theorem CyclicWeightModel.offsetSupport_contains [Nonempty A] (M : CyclicWeightModel d A) :
    (0 : Fin (d - 1) → ℕ) ∈ M.offsetSupport := by
  classical
  exact Finset.mem_image.mpr ⟨M.highestBasis, Finset.mem_univ _, M.weightCoeff_highest⟩

/-- The finite offset partition function is exactly the concrete basis sum. -/
theorem CyclicWeightModel.partitionFunction_eq_relativeNormalizer
    (M : CyclicWeightModel d A) (s : Finset (Fin (d - 1) → ℕ))
    (hs : M.offsetSupport ⊆ s) (ratio : Fin (d - 1) → ℝ) :
    partitionFunction s M.offsetMultiplicity (rootWeightMonomial ratio) = M.relativeNormalizer ratio := by
  classical
  calc
    _ = ∑ delta ∈ s, ∑ a : A with M.weightCoeff a = delta, M.relativeWeight ratio a := by
      apply Finset.sum_congr rfl
      intro delta _
      rw [M.offsetMultiplicity_eq_card]
      symm
      calc
        _ = ∑ a : A with M.weightCoeff a = delta, rootWeightMonomial ratio delta := by
          apply Finset.sum_congr rfl
          intro a ha
          exact congrArg (rootWeightMonomial ratio) (Finset.mem_filter.mp ha).2
        _ = _ := by simp [mul_comm]
    _ = _ := Finset.sum_fiberwise_of_maps_to
      (fun a ha => hs (Finset.mem_image.mpr ⟨a, ha, rfl⟩)) (M.relativeWeight ratio)

theorem CyclicWeightModel.offsetCoefficient_nonneg [Nonempty A]
    (M : CyclicWeightModel d A) (s : Finset (Fin (d - 1) → ℕ)) (hs : M.offsetSupport ⊆ s)
    (ratio : Fin (d - 1) → ℝ) (hratio : ∀ j, 0 ≤ ratio j) (delta : Fin (d - 1) → ℕ) :
    0 ≤ M.offsetCoefficient s ratio delta := by
  change 0 ≤ rootWeightMonomial ratio delta / partitionFunction s M.offsetMultiplicity _
  rw [M.partitionFunction_eq_relativeNormalizer s hs ratio]
  exact div_nonneg (rootWeightMonomial_nonneg ratio hratio delta)
    ((M.relativeNormalizer_ge_one ratio hratio).trans' (by norm_num))

theorem CyclicWeightModel.offsetCoefficient_envelope [Nonempty A]
    (M : CyclicWeightModel d A) (s : Finset (Fin (d - 1) → ℕ)) (hs : M.offsetSupport ⊆ s)
    (ratio : Fin (d - 1) → ℝ) (q : ℝ) (hratio : ∀ j, 0 ≤ ratio j) (hbound : ∀ j, ratio j ≤ q)
    (delta : Fin (d - 1) → ℕ) : M.offsetCoefficient s ratio delta ≤ q ^ depth delta := by
  change rootWeightMonomial ratio delta / partitionFunction s M.offsetMultiplicity _ ≤ _
  rw [M.partitionFunction_eq_relativeNormalizer s hs ratio]
  exact (div_le_self (rootWeightMonomial_nonneg ratio hratio delta)
    (M.relativeNormalizer_ge_one ratio hratio)).trans (rootWeightMonomial_envelope ratio q hratio hbound delta)

/-- The state block coefficients have total mass exactly one. -/
theorem CyclicWeightModel.offsetCoefficient_normalized [Nonempty A]
    (M : CyclicWeightModel d A) (s : Finset (Fin (d - 1) → ℕ)) (hs : M.offsetSupport ⊆ s)
    (ratio : Fin (d - 1) → ℝ) (hratio : ∀ j, 0 ≤ ratio j) :
    ∑ delta ∈ s, M.offsetCoefficient s ratio delta * (M.offsetMultiplicity delta : ℝ) = 1 := by
  apply coefficient_normalized
  rw [M.partitionFunction_eq_relativeNormalizer s hs ratio]
  have h := M.relativeNormalizer_ge_one ratio hratio
  linarith

/-- The actual diagonal state is precisely the finite weight-block mixture. -/
theorem CyclicWeightModel.mixture_offsetCoefficient_eq_relativeState
    (M : CyclicWeightModel d A) (s : Finset (Fin (d - 1) → ℕ)) (hs : M.offsetSupport ⊆ s)
    (ratio : Fin (d - 1) → ℝ) :
    mixture s (M.offsetCoefficient s ratio) (fun delta => weightProjector M.weight (M.row - offset delta)) =
      M.relativeState ratio := by
  classical
  ext a b
  by_cases hab : a = b
  · subst b
    simp only [mixture, Matrix.sum_apply, Pi.smul_apply, weightProjector,
      Matrix.diagonal_apply_eq, Complex.real_smul, smul_eq_mul, relativeState]
    have hmem : M.weightCoeff a ∈ s := hs (Finset.mem_image.mpr ⟨a, Finset.mem_univ _, rfl⟩)
    rw [Finset.sum_eq_single (M.weightCoeff a)]
    · have hw : M.weight a = M.row - offset (M.weightCoeff a) := (M.weight_iff_weightCoeff _ _).mpr rfl
      rw [Matrix.smul_apply, Matrix.diagonal_apply_eq, if_pos hw, Complex.real_smul, mul_one]
      simp only [offsetCoefficient, coefficient, M.partitionFunction_eq_relativeNormalizer s hs ratio, relativeWeight]
    · intro delta hdelta hne
      have hw : M.weight a ≠ M.row - offset delta := mt (M.weight_iff_weightCoeff a delta).mp (Ne.symm hne)
      rw [Matrix.smul_apply, Matrix.diagonal_apply_eq, if_neg hw, smul_zero]
    · exact fun hn => (hn hmem).elim
  · rw [relativeState, Matrix.diagonal_apply_ne _ hab]
    unfold mixture
    rw [Matrix.sum_apply]
    apply Finset.sum_eq_zero
    intro delta _
    simp only [WeightSectors.weightProjector, Matrix.smul_apply,
      Matrix.diagonal_apply_ne _ hab, smul_zero]


/-- Actual trace normalization follows from the proved finite block mass. -/
theorem CyclicWeightModel.mixture_offsetCoefficient_trace [Nonempty A]
    (M : CyclicWeightModel d A) (s : Finset (Fin (d - 1) → ℕ)) (hs : M.offsetSupport ⊆ s)
    (ratio : Fin (d - 1) → ℝ) (hratio : ∀ j, 0 ≤ ratio j) :
    (mixture s (M.offsetCoefficient s ratio) (fun delta => weightProjector M.weight (M.row - offset delta))).trace = 1 := by
  rw [M.mixture_offsetCoefficient_eq_relativeState s hs ratio]
  simp only [relativeState, Matrix.trace_diagonal, ← Complex.ofReal_sum]
  rw [← Finset.sum_div]
  change ((M.relativeNormalizer ratio / M.relativeNormalizer ratio : ℝ) : ℂ) = 1
  rw [div_self (by have h := M.relativeNormalizer_ge_one ratio hratio; linarith)]
  norm_num

/-- The ratio of any pair of normalized offset coefficient families is the
single ratio of their actual basis normalizers. -/
theorem offsetCoefficient_ratio {B : Type*} [Fintype B] [DecidableEq B] [Nonempty A]
    (M : CyclicWeightModel d A) (N : CyclicWeightModel d B)
    (s : Finset (Fin (d - 1) → ℕ)) (hsM : M.offsetSupport ⊆ s) (hsN : N.offsetSupport ⊆ s)
    (ratio : Fin (d - 1) → ℝ) (hratio : ∀ j, 0 ≤ ratio j) (delta : Fin (d - 1) → ℕ) :
    N.offsetCoefficient s ratio delta =
      (M.relativeNormalizer ratio / N.relativeNormalizer ratio) * M.offsetCoefficient s ratio delta := by
  have h := coefficient_ratio s M.offsetMultiplicity N.offsetMultiplicity (rootWeightMonomial ratio)
    (by rw [M.partitionFunction_eq_relativeNormalizer s hsM ratio]
        have h := M.relativeNormalizer_ge_one ratio hratio
        linarith) delta
  simpa only [M.partitionFunction_eq_relativeNormalizer s hsM ratio,
    N.partitionFunction_eq_relativeNormalizer s hsN ratio] using h

end FreeEntropy.CartanLieCloning
