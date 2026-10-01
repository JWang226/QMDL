/-
Copyright (c) 2026 Free Entropy formalization contributors.
See LICENSE and NOTICE in the repository root for license and attribution.
-/

import FreeEntropy.TensorWeightSource
import FreeEntropy.CyclicWeightHighest
import FreeEntropy.SchurWeylWeightMultiplicity

/-! Actual physical sectors with a common highest occupation admit
orthonormal highest columns in the literal word-type space. Their copy
count is therefore bounded without a tableau multiplicity identity. -/
noncomputable section
open Matrix
open scoped BigOperators
namespace FreeEntropy.SchurWeyl
open Occupation WordTypes
set_option backward.isDefEq.respectTransparency false
variable {d n : ℕ}

/-- The actual sectors having one prescribed highest occupation. -/
abbrev SectorsAt (lam : Occupation d n) := {i : Sector d n // sectorHighestOccupation i = lam}

instance (lam : Occupation d n) : Fintype (SectorsAt lam) := by
  classical
  exact inferInstanceAs (Fintype {i : Sector d n // sectorHighestOccupation i = lam})

theorem sectorWeightEmbedding_orthogonal (i j : Sector d n) (hij : i ≠ j) :
    (sectorWeightEmbedding i)ᴴ * sectorWeightEmbedding j = 0 := by
  have h := (physicalDecomposition d n).orthogonal i j hij
  simp only [sectorWeightEmbedding, Matrix.conjTranspose_mul, Matrix.mul_assoc,
    ← Matrix.mul_assoc ((physicalDecomposition d n).embedding i)ᴴ
      ((physicalDecomposition d n).embedding j), h, Matrix.zero_mul, Matrix.mul_zero]

/-- The distinguished highest coordinate has exactly the proved natural
highest occupation of this physical sector. -/
theorem sector_highestBasis_occupation (i : Sector d n) :
    sectorWeight i (sectorWeightModel i).highestBasis = sectorHighestOccupation i := by
  apply Subtype.ext
  funext j
  have h := congrFun (sectorWeightModel i).highestBasis_weight j
  change ((sectorWeight i (sectorWeightModel i).highestBasis).val j : ℝ) =
    ((sectorHighestOccupation i).val j : ℝ) at h
  exact_mod_cast h

def groupedHighestColumns (lam : Occupation d n) :
    Matrix (Fin n → Fin d) (SectorsAt lam) ℂ :=
  fun w i => sectorWeightEmbedding i.val w (sectorWeightModel i.val).highestBasis

theorem groupedHighestColumns_isometry (lam : Occupation d n) :
    (groupedHighestColumns lam)ᴴ * groupedHighestColumns lam = 1 := by
  classical
  ext i j
  change ((sectorWeightEmbedding i.val)ᴴ * sectorWeightEmbedding j.val)
    (sectorWeightModel i.val).highestBasis (sectorWeightModel j.val).highestBasis = _
  by_cases hij : i = j
  · subst j
    rw [sectorWeightEmbedding_isometry]
    simp
  · rw [sectorWeightEmbedding_orthogonal i.val j.val (fun h => hij (Subtype.ext h))]
    simp [hij]

/-- The actual number of irreducible copies with highest occupation `lam`
is bounded by the actual number of words of that content. -/
theorem sectorsAt_card_le_words (lam : Occupation d n) :
    Fintype.card (SectorsAt lam) ≤ Fintype.card (Words (n := n) lam.val) := by
  apply orthonormal_supported_card_le lam (groupedHighestColumns lam)
    (groupedHighestColumns_isometry lam)
  intro w hw i
  apply sectorWeightEmbedding_supported i.val (sectorWeightModel i.val).highestBasis w
  simpa only [sector_highestBasis_occupation, i.property] using hw

end FreeEntropy.SchurWeyl
