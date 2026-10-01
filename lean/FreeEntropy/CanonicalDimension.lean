/-
Copyright (c) 2026 Free Entropy formalization contributors.
See LICENSE and NOTICE in the repository root for license and attribution.
-/

import FreeEntropy.CanonicalCharacterIdentity
import FreeEntropy.WeylDimensionExtraction

/-! Weyl dimensions of the actual constructed irreducible representations.
The character identity and the finite determinant extraction discharge the
representation-dimension premise, including the padded memory target. -/
noncomputable section
open Filter
open scoped BigOperators Topology
namespace FreeEntropy.ExteriorRepresentation
set_option backward.isDefEq.respectTransparency false
variable {d r : ℕ}

/-- The actual canonical Hilbert space has exactly the GT cardinality. -/
theorem canonical_dimension_eq_GT (mu : Fin d → ℕ) (hmu : Antitone mu) (hd : 0 < d) :
    Module.finrank ℂ (highestSubspace mu) =
      Fintype.card (GelfandTsetlin.Pattern (fun i => (mu i : ℤ))) :=
  WeylCharacter.dimension_eq_GT_of_character_identity (canonicalCharacter mu) mu hmu
    (Module.finrank ℂ (highestSubspace mu)) (canonicalCharacter_eval_one mu)
    (canonicalCharacter_identity mu hmu hd)

theorem canonical_dimension_fullWeyl (mu : ℕ → ℕ)
    (hmu : Antitone (fun i : Fin d => mu i.val)) (hd : 0 < d) :
    (Module.finrank ℂ (highestSubspace (fun i : Fin d => mu i.val)) : ℝ) =
      Weyl.activeProduct d d (fun i => (mu i : ℝ)) := by
  rw [canonical_dimension_eq_GT _ hmu hd]
  apply GTDimension.card_eq_fullWeyl d (fun i => (mu i : ℤ))
  intro i j hij
  change (mu j.val : ℤ) ≤ (mu i.val : ℤ)
  exact_mod_cast hmu hij

theorem canonical_dimension_activeWeyl (mu : ℕ → ℕ)
    (hmu : Antitone (fun i : Fin d => mu i.val)) (hd : 0 < d) (hr : r ≤ d)
    (hzero : ∀ i, r ≤ i → i < d → mu i = 0) :
    (Module.finrank ℂ (highestSubspace (fun i : Fin d => mu i.val)) : ℝ) =
      Weyl.activeProduct d r (fun i => (mu i : ℝ)) := by
  rw [canonical_dimension_eq_GT _ hmu hd]
  apply GTDimension.card_eq_activeWeyl d r hr (fun i => (mu i : ℤ))
  · intro i j hij
    change (mu j.val : ℤ) ≤ (mu i.val : ℤ)
    exact_mod_cast hmu hij
  · intro i hi hid
    simp [hzero i hi hid]

/-- Natural coordinates of the manuscript's padded target. -/
def targetNaturalRow (s : FixedSpectrum d r) (n i : ℕ) : ℕ :=
  (GTDimension.targetIntegerRow s n i).toNat

@[simp] theorem targetNaturalRow_cast_int (s : FixedSpectrum d r) (n i : ℕ) :
    (targetNaturalRow s n i : ℤ) = GTDimension.targetIntegerRow s n i :=
  Int.toNat_of_nonneg (GTDimension.targetIntegerRow_nonneg s n i)

@[simp] theorem targetNaturalRow_cast (s : FixedSpectrum d r) (n i : ℕ) :
    (targetNaturalRow s n i : ℝ) = s.targetRow n i := by
  rw [← GTDimension.targetIntegerRow_cast]
  exact_mod_cast targetNaturalRow_cast_int s n i

theorem targetNaturalRow_antitone (s : FixedSpectrum d r) (n : ℕ) :
    Antitone (fun i : Fin d => targetNaturalRow s n i.val) := by
  intro i j hij
  exact Int.toNat_le_toNat (GTDimension.targetIntegerRow_dominant s n hij)

def targetCanonicalDimension (s : FixedSpectrum d r) (n : ℕ) : ℕ :=
  Module.finrank ℂ (highestSubspace (fun i : Fin d => targetNaturalRow s n i.val))

theorem targetCanonicalDimension_eq_GT (s : FixedSpectrum d r) (n : ℕ) :
    targetCanonicalDimension s n = GTDimension.targetDimension s n := by
  have hd : 0 < d := lt_of_lt_of_le s.rank_pos s.rank_le
  unfold targetCanonicalDimension
  rw [canonical_dimension_eq_GT _ (targetNaturalRow_antitone s n) hd]
  simp only [targetNaturalRow_cast_int, GTDimension.targetDimension]

theorem targetCanonicalDimension_pos (s : FixedSpectrum d r) (n : ℕ) :
    0 < targetCanonicalDimension s n := irrep_dimension_pos _

theorem targetCanonicalDimension_weyl (s : FixedSpectrum d r) (n : ℕ) :
    (targetCanonicalDimension s n : ℝ) = Weyl.activeProduct d r (s.targetRow n) := by
  rw [targetCanonicalDimension_eq_GT, GTDimension.targetDimension_weyl]

/-- The exact asymptotic memory formula for the actual canonical target. -/
theorem targetCanonicalDimension_log_asymptotic (s : FixedSpectrum d r) :
    Tendsto (fun n => Real.logb 2 (targetCanonicalDimension s n) -
      Weyl.qmdl d r s.eigenvalue n) atTop (𝓝 0) := by
  simpa only [targetCanonicalDimension_eq_GT] using GTDimension.targetDimension_log_asymptotic s

end FreeEntropy.ExteriorRepresentation
