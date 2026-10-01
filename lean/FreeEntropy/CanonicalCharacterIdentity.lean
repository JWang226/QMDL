/-
Copyright (c) 2026 Free Entropy formalization contributors.
See LICENSE and NOTICE in the repository root for license and attribution.
-/

import FreeEntropy.WeylCharacterSupport
import FreeEntropy.WeylAlternantCoefficients
import FreeEntropy.WeylAlternating

/-! The actual canonical character satisfies the Weyl alternant identity.
The proof combines the radial Casimir equation, the integral root cone,
actual variable-permutation symmetry, and the one-dimensional highest line. -/
noncomputable section
open scoped BigOperators
namespace FreeEntropy.ExteriorRepresentation
open MvPolynomial WeylCharacter
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
variable {d : ℕ}

/-- Sorting an actual nonzero numerator exponent recovers the highest shifted
row, so the entire support lies on its permutation orbit. -/
theorem canonicalCharacter_numerator_support_orbit (mu : Fin d → ℕ) (hmu : Antitone mu)
    (hd : 0 < d) (m : Fin d →₀ ℕ)
    (hm : coeff m (denominator d * canonicalCharacter mu) ≠ 0) :
    ∃ e : Equiv.Perm (Fin d), m = (WeylCharacter.exponent (shiftedHighest mu)).mapDomain e := by
  have hp : IsAlternating (denominator d * canonicalCharacter mu) :=
    canonical_denominator_character_alternating mu
  let s := Tuple.sort (α := OrderDual ℕ) (fun i => m i)
  have hs : Antitone (fun i => m (s i)) := Tuple.monotone_sort (α := OrderDual ℕ) (fun i => m i)
  have hi : Function.Injective (fun i => m (s i)) := (hp.support_injective m hm).comp s.injective
  have hanti : StrictAnti (fun i => (m.mapDomain s.symm) i) := by
    simpa only [Finsupp.mapDomain_equiv_apply, Equiv.symm_symm] using hs.strictAnti_of_injective hi
  have hm' : coeff (m.mapDomain s.symm) (denominator d * canonicalCharacter mu) ≠ 0 :=
    (hp.coeff_permutation_ne_zero m s.symm).mpr hm
  have he := canonicalCharacter_strictAnti_exponent mu hmu hd (m.mapDomain s.symm) hm' hanti
  refine ⟨s, ?_⟩
  rw [← he]
  ext i
  simp only [Finsupp.mapDomain_equiv_apply, Equiv.symm_symm, Equiv.apply_symm_apply]

/-- Pointedness of the positive-root cone makes the top coefficient a product
of the two actual highest coefficients. -/
theorem canonicalCharacter_numerator_highest_coeff (mu : Fin d → ℕ) (hmu : Antitone mu) :
    coeff (WeylCharacter.exponent (shiftedHighest mu)) (denominator d * canonicalCharacter mu) =
      (Equiv.Perm.sign (Fin.revPerm (n := d)) : ℤ) := by
  let rho : Fin d → ℕ := fun i => d - 1 - i.val
  have hr : (fun i => (rho i : ℝ)) = staircase := by
    funext i
    have h := shiftedHighest_cast (fun _ : Fin d => 0) i
    simpa only [shiftedHighest, zero_add, Nat.cast_zero] using h
  have hp : Below (fun i => (rho i : ℝ)) (denominator d) := by
    rw [hr]
    exact below_denominator d
  have hq : Below (fun i => (mu i : ℝ)) (canonicalCharacter mu) := canonicalCharacter_root_cone mu hmu
  have he : rho + mu = shiftedHighest mu := by funext i; simp [rho, shiftedHighest, Nat.add_comm]
  have hc : coeff (WeylCharacter.exponent mu) (canonicalCharacter mu) = 1 :=
    canonicalCharacter_highest_coeff mu hmu
  rw [← he, coeff_mul_highest rho mu _ _ hp hq, hc, mul_one]
  exact denominator_highest_coeff d

end FreeEntropy.ExteriorRepresentation

namespace FreeEntropy.WeylCharacter
open MvPolynomial
set_option backward.isDefEq.respectTransparency false
variable {d : ℕ}

/-- The target alternant has the same exponent orbit as its highest row. -/
theorem highest_alternant_support_orbit (mu : Fin d → ℕ) (m : Fin d →₀ ℕ)
    (hm : coeff m (alternant (ascendingHighest mu)) ≠ 0) :
    ∃ e : Equiv.Perm (Fin d), m = (exponent (shiftedHighest mu)).mapDomain e := by
  obtain ⟨e, he⟩ := alternant_support_orbit (ascendingHighest mu) m hm
  refine ⟨(Fin.revPerm (n := d)).trans e, ?_⟩
  rw [he]
  ext i
  simp only [Finsupp.mapDomain_equiv_apply, exponent_apply]
  change ascendingHighest mu (e.symm i) = shiftedHighest mu ((Fin.revPerm (n := d)).symm (e.symm i))
  rw [← ascendingHighest_reverse mu]
  simp [Fin.revPerm_symm]

end FreeEntropy.WeylCharacter

namespace FreeEntropy.ExteriorRepresentation
open MvPolynomial WeylCharacter
variable {d : ℕ}

/-- The Weyl character identity for the actual, constructed canonical
irreducible representation. It is derived from its Lie operators and weights,
not assumed as a representation-theoretic formula. -/
theorem canonicalCharacter_identity (mu : Fin d → ℕ) (hmu : Antitone mu) (hd : 0 < d) :
    denominator d * canonicalCharacter mu = alternant (ascendingHighest mu) := by
  apply (canonical_denominator_character_alternating mu).ext_of_support_orbit
    (alternant_alternating (ascendingHighest mu)) (WeylCharacter.exponent (shiftedHighest mu))
    (canonicalCharacter_numerator_support_orbit mu hmu hd) (highest_alternant_support_orbit mu)
  exact (canonicalCharacter_numerator_highest_coeff mu hmu).trans (alternant_highest_coeff mu hmu).symm

end FreeEntropy.ExteriorRepresentation

namespace FreeEntropy.ExteriorRepresentation
open MvPolynomial WeylCharacter
variable {d : ℕ}

/-- The zero-dimensional alphabet is included by the same highest-coefficient
identity, so the character formula holds in every finite dimension. -/
theorem canonicalCharacter_identity_all (mu : Fin d → ℕ) (hmu : Antitone mu) :
    denominator d * canonicalCharacter mu = alternant (ascendingHighest mu) := by
  by_cases hd : 0 < d
  · exact canonicalCharacter_identity mu hmu hd
  · have hd0 : d = 0 := Nat.eq_zero_of_not_pos hd
    subst d
    apply MvPolynomial.ext
    intro m
    have he : m = WeylCharacter.exponent (shiftedHighest mu) := by
      ext i
      exact Fin.elim0 i
    rw [he]
    exact (canonicalCharacter_numerator_highest_coeff mu hmu).trans (alternant_highest_coeff mu hmu).symm

end FreeEntropy.ExteriorRepresentation
