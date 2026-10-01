/-
Copyright (c) 2026 Free Entropy formalization contributors.
See LICENSE and NOTICE in the repository root for license and attribution.
-/

import FreeEntropy.TensorWeightCoordinates
import FreeEntropy.LiePBWWeights
import FreeEntropy.CartanLieCloning

/-! The highest-weight matrix model is now constructed from an actual
physical tensor sector. Diagonal coordinates, highest vector, cyclicity,
dominance, and the positive root cone are conclusions of prior proofs. -/
noncomputable section
open Matrix

namespace FreeEntropy.SchurWeyl
open Occupation CasimirWeights
set_option backward.isDefEq.respectTransparency false
variable {d n : ℕ}

def sectorHighestOccupation (i : Sector d n) : Occupation d n :=
  (exists_sector_weight_highest i).choose

def sectorWeightHighestVector (i : Sector d n) : SectorSpace d n i → ℂ :=
  (exists_sector_weight_highest i).choose_spec.choose

theorem sectorWeightHighestVector_spec (i : Sector d n) :
    sectorWeightHighestVector i ≠ 0 ∧ Antitone (sectorHighestOccupation i).val ∧
    (∀ j, (sectorWeightGenerators i).E j j *ᵥ sectorWeightHighestVector i =
      ((sectorHighestOccupation i).val j : ℂ) • sectorWeightHighestVector i) ∧
    (∀ j k, j < k → (sectorWeightGenerators i).E j k *ᵥ sectorWeightHighestVector i = 0) ∧
    LiePBW.cyclicSpan (sectorWeightGenerators i) (sectorWeightHighestVector i) = ⊤ :=
  (exists_sector_weight_highest i).choose_spec.choose_spec

/-- Every actual basis weight lies below the actual highest occupation by
an integral nonnegative combination of simple roots. -/
theorem sectorWeight_in_root_cone (i : Sector d n) (b : SectorSpace d n i) :
    ∃ c : Fin (d - 1) → ℕ,
      (fun j => ((sectorHighestOccupation i).val j : ℝ)) -
        (fun j => ((sectorWeight i b).val j : ℝ)) = offset c := by
  obtain ⟨_, _, hw, hr, hc⟩ := sectorWeightHighestVector_spec i
  apply LiePBW.weight_in_root_cone (sectorWeightGenerators i)
    (fun j => ((sectorHighestOccupation i).val j : ℝ))
    (fun j => ((sectorWeight i b).val j : ℝ))
    (sectorWeightHighestVector i) (Pi.single b (1 : ℂ))
  · intro j
    simpa using hw j
  · exact hr
  · rw [hc]; trivial
  · intro h
    have h' := congrFun h b
    simp at h'
  · intro j
    rw [sectorWeightGenerators_diagonal]
    ext k
    by_cases h : k = b
    · subst k; simp
    · simp [Matrix.mulVec_diagonal, h]

/-- Chosen coefficients of the proved positive simple-root difference. -/
def sectorWeightCoefficients (i : Sector d n) (b : SectorSpace d n i) : Fin (d - 1) → ℕ :=
  (sectorWeight_in_root_cone i b).choose

theorem sectorWeightCoefficients_spec (i : Sector d n) (b : SectorSpace d n i) :
    (fun j => ((sectorHighestOccupation i).val j : ℝ)) -
      (fun j => ((sectorWeight i b).val j : ℝ)) = offset (sectorWeightCoefficients i b) :=
  (sectorWeight_in_root_cone i b).choose_spec

/-- A fully constructed weight model for every actual physical tensor
sector. There are no diagonal-basis, cyclicity, or root-cone premises. -/
def sectorWeightModel (i : Sector d n) :
    CartanLieCloning.CyclicWeightModel d (SectorSpace d n i) where
  generators := sectorWeightGenerators i
  row j := ((sectorHighestOccupation i).val j : ℝ)
  weight b j := ((sectorWeight i b).val j : ℝ)
  highest b _ := sectorWeightHighestVector i b
  diagonal j := by
    simpa only [WeightSectors.weightDiagonal, Complex.ofReal_natCast] using
      sectorWeightGenerators_diagonal i j
  highest_weight j := by
    ext b u
    simpa using congrFun ((sectorWeightHighestVector_spec i).2.2.1 j) b
  highest_raise j k hjk := by
    ext b u
    exact congrFun ((sectorWeightHighestVector_spec i).2.2.2.1 j k hjk) b
  cyclic := (sectorWeightGenerators i).column_cyclic_of_vector
    (sectorWeightHighestVector i) (sectorWeightHighestVector_spec i).2.2.2.2
  dominant j := by
    exact_mod_cast (sectorWeightHighestVector_spec i).2.1 (show left j ≤ right j by
      change j.val ≤ j.val + 1
      omega)
  weightCoeff := sectorWeightCoefficients i
  weight_cone := sectorWeightCoefficients_spec i

@[simp] theorem sectorWeightModel_generators (i : Sector d n) :
    (sectorWeightModel i).generators = sectorWeightGenerators i := rfl

@[simp] theorem sectorWeightModel_row (i : Sector d n) (j : Fin d) :
    (sectorWeightModel i).row j = ((sectorHighestOccupation i).val j : ℝ) := rfl

@[simp] theorem sectorWeightModel_weight (i : Sector d n) (b : SectorSpace d n i) (j : Fin d) :
    (sectorWeightModel i).weight b j = ((sectorWeight i b).val j : ℝ) := rfl

end FreeEntropy.SchurWeyl
