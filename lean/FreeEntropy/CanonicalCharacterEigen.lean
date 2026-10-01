/-
Copyright (c) 2026 Free Entropy formalization contributors.
See LICENSE and NOTICE in the repository root for license and attribution.
-/

import FreeEntropy.CanonicalCharacter
import FreeEntropy.WeylDifferentialProduct

/-! The actual canonical character times the Weyl denominator is a genuine
flat Euler-Laplacian eigenpolynomial, with the highest shifted energy. -/
noncomputable section
open scoped BigOperators
namespace FreeEntropy.WeylCharacter
open MvPolynomial
set_option backward.isDefEq.respectTransparency false
variable {d : ℕ}

theorem denominator_character_eigen (p : MvPolynomial (Fin d) ℂ) (c : ℂ) (n : ℕ)
    (hdegree : (∑ i, euler i p) = (n : ℂ) • p)
    (hradial : denominator d * (C c * p - laplacian p) =
      ∑ r ∈ positiveRoots d, denominatorWithout r * (X r.1 + X r.2) *
        (euler r.2 p - euler r.1 p)) :
    laplacian (denominator d * p) =
      (c + (d - 1 : ℕ) * (n : ℂ) + ∑ i : Fin d, (i.val : ℂ) ^ 2) • (denominator d * p) := by
  rw [laplacian_mul, denominator_laplacian, denominator_cross_radial,
    hdegree, ← hradial]
  simp only [← Nat.cast_smul_eq_nsmul ℂ, Algebra.smul_def, MvPolynomial.algebraMap_eq,
    map_add, map_mul, map_natCast]
  ring

/-- The descending highest exponent of the actual Weyl numerator. -/
def shiftedHighest (mu : Fin d → ℕ) : Fin d → ℕ := fun i => mu i + (d - 1 - i.val)

theorem shiftedHighest_energy (mu : Fin d → ℕ) (hd : 0 < d) :
    (CasimirWeights.casimir (fun i => (mu i : ℝ)) : ℂ) +
      (d - 1 : ℕ) * ((∑ i, mu i : ℕ) : ℂ) + (∑ i : Fin d, (i.val : ℂ) ^ 2) =
      (∑ i : Fin d, shiftedHighest mu i ^ 2 : ℕ) := by
  have hrho : (∑ i : Fin d, staircase i ^ 2) = ∑ i : Fin d, (i.val : ℝ) ^ 2 := by
    have he := Equiv.sum_comp (Fin.revPerm (n := d)) (fun i : Fin d => (i.val : ℝ) ^ 2)
    convert he using 1
    apply Finset.sum_congr rfl
    intro i _
    congr 1
    simp only [staircase, Fin.revPerm_apply, Fin.val_rev]
    rw [Nat.cast_sub (by have := i.isLt; omega), Nat.cast_add]
    norm_num
    ring
  have hs (i : Fin d) : (shiftedHighest mu i : ℝ) = (mu i : ℝ) + staircase i := by
    simp only [shiftedHighest, Nat.cast_add, staircase]
    rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]
    norm_num
  have he := shiftedEnergy_eq (fun i => (mu i : ℝ))
  rw [hrho] at he
  have hd' : ((d - 1 : ℕ) : ℝ) = (d : ℝ) - 1 := by rw [Nat.cast_sub (by omega)]; norm_num
  have he' : CasimirWeights.casimir (fun i => (mu i : ℝ)) +
      ((d - 1 : ℕ) : ℝ) * (∑ i, (mu i : ℝ)) + (∑ i : Fin d, (i.val : ℝ) ^ 2) =
      (∑ i : Fin d, (shiftedHighest mu i : ℝ) ^ 2) := by
    simpa only [shiftedEnergy, hs, hd'] using he.symm
  exact_mod_cast he'

end FreeEntropy.WeylCharacter

namespace FreeEntropy.ExteriorRepresentation
open WeylCharacter
set_option backward.isDefEq.respectTransparency false
variable {d : ℕ}

/-- Flat eigenpolynomial identity for the literal canonical character. -/
theorem canonicalCharacter_eigen (mu : Fin d → ℕ) (hmu : Antitone mu) (hd : 0 < d) :
    laplacian (denominator d * canonicalCharacter mu) =
      ((∑ i : Fin d, shiftedHighest mu i ^ 2 : ℕ) : ℂ) •
        (denominator d * canonicalCharacter mu) := by
  have h := denominator_character_eigen (canonicalCharacter mu)
    (CasimirWeights.casimir (fun i => (mu i : ℝ)) : ℂ) (∑ i, mu i)
    (canonicalCharacter_total_euler mu hmu) (canonicalCharacter_radial mu hmu)
  rwa [shiftedHighest_energy mu hd] at h

theorem canonicalCharacter_numerator_energy (mu : Fin d → ℕ) (hmu : Antitone mu) (hd : 0 < d)
    (m : Fin d →₀ ℕ) (hm : MvPolynomial.coeff m (denominator d * canonicalCharacter mu) ≠ 0) :
    exponentEnergy m = ∑ i : Fin d, shiftedHighest mu i ^ 2 :=
  eigenpolynomial_support_energy _ _ (canonicalCharacter_eigen mu hmu hd) m hm

end FreeEntropy.ExteriorRepresentation
