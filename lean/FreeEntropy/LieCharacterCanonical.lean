/-
Copyright (c) 2026 Free Entropy formalization contributors.
See LICENSE and NOTICE in the repository root for license and attribution.
-/

import FreeEntropy.LieCharacterSymmetry
import FreeEntropy.LieCharacterFinite

/-! Permuted weights and all permuted character support obey the actual
canonical highest root cone. These are consequences of proved symmetry. -/
noncomputable section
open scoped BigOperators
namespace FreeEntropy.LieCharacter
set_option backward.isDefEq.respectTransparency false
variable {d : ℕ} {H : Type*} [Fintype H] [DecidableEq H]

/-- Every occurring basis weight has a nonzero literal character coefficient. -/
theorem character_coeff_weight_ne_zero (weight : H → Fin d → ℕ) (a : H) :
    MvPolynomial.coeff (exponent (weight a)) (character weight) ≠ 0 := by
  classical
  rw [character_coeff]
  have hp : 0 < (Finset.univ.filter (fun h => exponent (weight h) = exponent (weight a))).card :=
    Finset.card_pos.mpr ⟨a, by simp⟩
  exact_mod_cast hp.ne'

/-- Variable symmetry implies permutation closure of the actual weight
multiset, witnessed by another actual basis coordinate. -/
theorem exists_permuted_weight (weight : H → Fin d → ℕ)
    (hsym : ∀ e : Equiv.Perm (Fin d), MvPolynomial.rename e (character weight) = character weight)
    (a : H) (e : Equiv.Perm (Fin d)) : ∃ b : H, weight b = weight a ∘ e := by
  have hm := MvPolynomial.coeff_rename_mapDomain e.symm e.symm.injective
    (character weight) (exponent (weight a))
  rw [hsym] at hm
  have hn : MvPolynomial.coeff ((exponent (weight a)).mapDomain e.symm) (character weight) ≠ 0 :=
    hm.trans_ne (character_coeff_weight_ne_zero weight a)
  obtain ⟨b, hb⟩ := exists_weight_of_coeff_ne_zero weight _ hn
  refine ⟨b, ?_⟩
  funext i
  have hi := congrArg (fun m : Fin d →₀ ℕ => m i) hb
  simpa only [exponent, Finsupp.coe_equivFunOnFinite_symm, Finsupp.mapDomain_equiv_apply,
    Equiv.symm_symm, Function.comp_apply] using hi

end FreeEntropy.LieCharacter
namespace FreeEntropy.ExteriorRepresentation
open LieCharacter
set_option backward.isDefEq.respectTransparency false
variable {d : ℕ}

theorem canonicalWeight_permuted (mu : Fin d → ℕ) (a : IrrepIndex mu)
    (e : Equiv.Perm (Fin d)) : ∃ b : IrrepIndex mu,
      canonicalWeight mu b = canonicalWeight mu a ∘ e :=
  exists_permuted_weight (canonicalWeight mu) (canonical_character_rename mu) a e

/-- Every permutation of every actual character support weight lies below
its prescribed highest row in the integral positive simple-root cone. -/
theorem canonical_character_permuted_root_cone (mu : Fin d → ℕ) (hmu : Antitone mu)
    (m : Fin d →₀ ℕ) (hm : MvPolynomial.coeff m (LieCharacter.character (canonicalWeight mu)) ≠ 0)
    (e : Equiv.Perm (Fin d)) :
    ∃ c : Fin (d - 1) → ℕ,
      (fun i => (mu i : ℝ)) - (fun i => (m (e i) : ℝ)) = CasimirWeights.offset c := by
  have he := MvPolynomial.coeff_rename_mapDomain e.symm e.symm.injective
    (LieCharacter.character (canonicalWeight mu)) m
  rw [canonical_character_rename] at he
  have hne : MvPolynomial.coeff (m.mapDomain e.symm)
      (LieCharacter.character (canonicalWeight mu)) ≠ 0 := he.trans_ne hm
  obtain ⟨c, hc⟩ := cyclic_character_root_cone (canonicalWeightModel mu) (canonicalWeight mu)
    (fun a i => congrFun (canonicalWeight_spec mu a) i) (m.mapDomain e.symm) hne
  refine ⟨c, ?_⟩
  simpa only [canonicalWeightModel_row mu hmu, Finsupp.mapDomain_equiv_apply,
    Equiv.symm_symm] using hc

/-- In particular the root-cone domination holds for each permuted actual
basis weight, with no support or cone premise. -/
theorem canonicalWeight_permuted_root_cone (mu : Fin d → ℕ) (hmu : Antitone mu)
    (a : IrrepIndex mu) (e : Equiv.Perm (Fin d)) :
    ∃ c : Fin (d - 1) → ℕ,
      (fun i => (mu i : ℝ)) - (fun i => (canonicalWeight mu a (e i) : ℝ)) =
        CasimirWeights.offset c := by
  simpa only [exponent, Finsupp.coe_equivFunOnFinite_symm] using
    canonical_character_permuted_root_cone mu hmu (exponent (canonicalWeight mu a))
      (character_coeff_weight_ne_zero (canonicalWeight mu) a) e

end FreeEntropy.ExteriorRepresentation
