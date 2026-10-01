/-
Copyright (c) 2026 Free Entropy formalization contributors.
See LICENSE and NOTICE in the repository root for license and attribution.
-/

import FreeEntropy.CyclicWeightStateBlocks
import FreeEntropy.RankRootCounting

/-! Concrete normalized states with a zero spectral tail. All terms outside
the positive-rank root cone vanish, so only its actual finite weight blocks
enter the cloning estimate. -/
noncomputable section
open scoped BigOperators
open Matrix
namespace FreeEntropy.CartanLieCloning
open CasimirWeights WeightSectors CloningMatrices ExteriorRepresentation
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
variable {d : ℕ} {A : Type*} [Fintype A] [DecidableEq A]
local instance (rank : ℕ) : DecidablePred (SupportedSimpleOffset (d := d) rank) := Classical.decPred _

def CyclicWeightModel.relativeCoefficient (M : CyclicWeightModel d A)
    (ratio : Fin (d - 1) → ℝ) (delta : Fin (d - 1) → ℕ) : ℝ :=
  rootWeightMonomial ratio delta / M.relativeNormalizer ratio

theorem CyclicWeightModel.relativeCoefficient_eq_offsetCoefficient
    (M : CyclicWeightModel d A) (ratio : Fin (d - 1) → ℝ)
    (s : Finset (Fin (d - 1) → ℕ)) (hs : M.offsetSupport ⊆ s) :
    M.relativeCoefficient ratio = M.offsetCoefficient s ratio := by
  funext delta
  unfold relativeCoefficient offsetCoefficient WeightNormalization.coefficient
  rw [M.partitionFunction_eq_relativeNormalizer s hs ratio]

theorem rootWeightMonomial_eq_zero_of_not_supported (rank : ℕ)
    (ratio : Fin (d - 1) → ℝ) (hzero : ∀ j, rank ≤ j.val + 1 → ratio j = 0)
    (delta : Fin (d - 1) → ℕ) (hdelta : ¬SupportedSimpleOffset rank delta) :
    rootWeightMonomial ratio delta = 0 := by
  classical
  obtain ⟨j, hj⟩ := not_forall.mp hdelta
  have hj' : rank ≤ j.val + 1 := (_root_.not_imp.mp hj).1
  have hdj : delta j ≠ 0 := (_root_.not_imp.mp hj).2
  exact Finset.prod_eq_zero (Finset.mem_univ j) (by rw [hzero j hj', zero_pow hdj])

theorem CyclicWeightModel.relativeCoefficient_nonneg [Nonempty A]
    (M : CyclicWeightModel d A) (ratio : Fin (d - 1) → ℝ) (hratio : ∀ j, 0 ≤ ratio j)
    (delta : Fin (d - 1) → ℕ) : 0 ≤ M.relativeCoefficient ratio delta := by
  rw [M.relativeCoefficient_eq_offsetCoefficient ratio M.offsetSupport (fun _ h => h)]
  exact M.offsetCoefficient_nonneg _ (fun _ h => h) ratio hratio delta

theorem CyclicWeightModel.relativeCoefficient_envelope [Nonempty A]
    (M : CyclicWeightModel d A) (ratio : Fin (d - 1) → ℝ) (q : ℝ)
    (hratio : ∀ j, 0 ≤ ratio j) (hbound : ∀ j, ratio j ≤ q) (delta : Fin (d - 1) → ℕ) :
    M.relativeCoefficient ratio delta ≤ q ^ depth delta := by
  rw [M.relativeCoefficient_eq_offsetCoefficient ratio M.offsetSupport (fun _ h => h)]
  exact M.offsetCoefficient_envelope _ (fun _ h => h) ratio q hratio hbound delta

theorem relativeCoefficient_ratio {B : Type*} [Fintype B] [DecidableEq B] [Nonempty A]
    (M : CyclicWeightModel d A) (N : CyclicWeightModel d B)
    (ratio : Fin (d - 1) → ℝ) (hratio : ∀ j, 0 ≤ ratio j) (delta : Fin (d - 1) → ℕ) :
    N.relativeCoefficient ratio delta =
      (M.relativeNormalizer ratio / N.relativeNormalizer ratio) * M.relativeCoefficient ratio delta := by
  have hM : M.relativeNormalizer ratio ≠ 0 := by
    have h := M.relativeNormalizer_ge_one ratio hratio
    linarith
  unfold CyclicWeightModel.relativeCoefficient
  field_simp

theorem CyclicWeightModel.supported_mixture_eq_relativeState
    (M : CyclicWeightModel d A) (ratio : Fin (d - 1) → ℝ) (rank : ℕ)
    (hzero : ∀ j, rank ≤ j.val + 1 → ratio j = 0)
    (s : Finset (Fin (d - 1) → ℕ)) (hs : M.offsetSupport ⊆ s) :
    mixture (s.filter (SupportedSimpleOffset rank)) (M.relativeCoefficient ratio)
      (fun delta => weightProjector M.weight (M.row - offset delta)) = M.relativeState ratio := by
  classical
  rw [← M.mixture_offsetCoefficient_eq_relativeState s hs ratio,
    ← M.relativeCoefficient_eq_offsetCoefficient ratio s hs]
  unfold mixture
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro delta hd hnot
  have hn : ¬SupportedSimpleOffset rank delta := by simpa only [Finset.mem_filter, hd, true_and] using hnot
  rw [relativeCoefficient, rootWeightMonomial_eq_zero_of_not_supported rank ratio hzero delta hn,
    zero_div, zero_smul]

theorem CyclicWeightModel.relativeState_trace [Nonempty A]
    (M : CyclicWeightModel d A) (ratio : Fin (d - 1) → ℝ) (hratio : ∀ j, 0 ≤ ratio j) :
    (M.relativeState ratio).trace = 1 := by
  rw [← M.mixture_offsetCoefficient_eq_relativeState M.offsetSupport (fun _ h => h) ratio]
  exact M.mixture_offsetCoefficient_trace _ (fun _ h => h) ratio hratio

end FreeEntropy.CartanLieCloning
