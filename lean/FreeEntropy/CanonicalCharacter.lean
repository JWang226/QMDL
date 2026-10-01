/-
Copyright (c) 2026 Free Entropy formalization contributors.
See LICENSE and NOTICE in the repository root for license and attribution.
-/

import FreeEntropy.LieCharacterFinite
import FreeEntropy.ExteriorWeightCoordinates

/-! Literal polynomial characters of the actual constructed canonical irreps.
Every degree, highest coefficient, root-cone, dimension and radial property
is proved from their actual orthonormal weight coordinates. -/
noncomputable section
open scoped BigOperators
namespace FreeEntropy.ExteriorRepresentation
open LieCharacter
set_option backward.isDefEq.respectTransparency false
variable {d : ℕ}
local instance canonicalCharacter_nonempty (mu : Fin d → ℕ) : Nonempty (IrrepIndex mu) :=
  Fin.pos_iff_nonempty.mp (irrep_dimension_pos mu)

def canonicalCharacter (mu : Fin d → ℕ) : MvPolynomial (Fin d) ℂ := LieCharacter.character (canonicalWeight mu)

@[simp] theorem canonicalCharacter_eval_one (mu : Fin d → ℕ) :
    MvPolynomial.eval (fun _ => (1 : ℂ)) (canonicalCharacter mu) =
      Module.finrank ℂ (highestSubspace mu) := by
  rw [canonicalCharacter, character_eval_one]
  simp

theorem canonicalCharacter_total_euler (mu : Fin d → ℕ) (hmu : Antitone mu) :
    (∑ i, WeylCharacter.euler i (canonicalCharacter mu)) =
      ((∑ i, mu i : ℕ) : ℂ) • canonicalCharacter mu :=
  character_total_euler (canonicalWeight mu) (∑ i, mu i) (canonicalWeight_sum mu hmu)

theorem canonicalCharacter_highest_coeff (mu : Fin d → ℕ) (hmu : Antitone mu) :
    MvPolynomial.coeff (LieCharacter.exponent mu) (canonicalCharacter mu) = 1 :=
  cyclic_character_highest_coeff (canonicalWeightModel mu) (canonicalWeight mu)
    (fun a i => congrFun (canonicalWeight_spec mu a) i) mu
    (fun i => congrFun (canonicalWeightModel_row mu hmu) i)

theorem canonicalCharacter_root_cone (mu : Fin d → ℕ) (hmu : Antitone mu)
    (m : Fin d →₀ ℕ) (hm : MvPolynomial.coeff m (canonicalCharacter mu) ≠ 0) :
    ∃ c : Fin (d - 1) → ℕ, (fun i => (mu i : ℝ)) - (fun i => (m i : ℝ)) =
      CasimirWeights.offset c := by
  have h := cyclic_character_root_cone (canonicalWeightModel mu) (canonicalWeight mu)
    (fun a i => congrFun (canonicalWeight_spec mu a) i) m hm
  rwa [canonicalWeightModel_row mu hmu] at h

theorem canonicalCharacter_support_degree (mu : Fin d → ℕ) (hmu : Antitone mu)
    (m : Fin d →₀ ℕ) (hm : MvPolynomial.coeff m (canonicalCharacter mu) ≠ 0) :
    (∑ i, m i) = ∑ i, mu i := by
  obtain ⟨h, hh⟩ := exists_weight_of_coeff_ne_zero (canonicalWeight mu) m hm
  rw [← hh]
  exact canonicalWeight_sum mu hmu h

/-- The genuine canonical irrep satisfies the full denominator-cleared
radial Casimir equation with its actual prescribed highest row. -/
theorem canonicalCharacter_radial (mu : Fin d → ℕ) (hmu : Antitone mu) :
    WeylCharacter.denominator d *
        (MvPolynomial.C (CasimirWeights.casimir (fun i => (mu i : ℝ)) : ℂ) * canonicalCharacter mu -
          WeylCharacter.laplacian (canonicalCharacter mu)) =
      ∑ p ∈ positiveRoots d, rootProductExcept p *
        (MvPolynomial.X p.1 + MvPolynomial.X p.2) *
        (WeylCharacter.euler p.2 (canonicalCharacter mu) - WeylCharacter.euler p.1 (canonicalCharacter mu)) := by
  have h := cyclic_radial_identity (canonicalWeightModel mu) (canonicalWeight mu)
    (fun a i => congrFun (canonicalWeight_spec mu a) i)
  rwa [rootProduct_eq_denominator, canonicalWeightModel_row mu hmu] at h

end FreeEntropy.ExteriorRepresentation
