/-
Copyright (c) 2026 Free Entropy formalization contributors.
See LICENSE and NOTICE in the repository root for license and attribution.
-/

import FreeEntropy.LieCharacterRadial
import FreeEntropy.WeylDenominator
import FreeEntropy.CyclicWeightHighest

/-! The literal character has the representation's actual dimension at the
identity, fixed degree, a unique highest monomial, and the proved root cone. -/
noncomputable section
open Matrix
open scoped BigOperators
namespace FreeEntropy.LieCharacter
set_option backward.isDefEq.respectTransparency false
variable {d : ℕ} {H : Type*} [Fintype H] [DecidableEq H]

theorem rootProduct_eq_denominator (d : ℕ) : rootProduct d = WeylCharacter.denominator d := by
  rw [WeylCharacter.denominator_product]
  simp only [rootProduct, positiveRoots, Finset.prod_filter, Fintype.prod_prod_type, rootFactor]
  apply Finset.prod_congr rfl
  intro i _
  rw [← Finset.prod_filter]
  congr 1
  ext j
  simp

@[simp] theorem character_eval_one (weight : H → Fin d → ℕ) :
    MvPolynomial.eval (fun _ => (1 : ℂ)) (character weight) = Fintype.card H := by
  simp [character, weightMonomial, MvPolynomial.eval_monomial]

theorem character_total_euler (weight : H → Fin d → ℕ) (n : ℕ)
    (hweight : ∀ h, ∑ i, weight h i = n) :
    (∑ i, WeylCharacter.euler i (character weight)) = (n : ℂ) • character weight := by
  simp only [euler_character, moment]
  rw [Finset.sum_comm]
  simp_rw [← Finset.sum_mul, ← map_sum]
  have hn (h : H) : (∑ i : Fin d, (weight h i : ℂ)) = n := by exact_mod_cast hweight h
  simp only [hn, ← Finset.mul_sum]
  rw [Algebra.smul_def]
  rfl

theorem cyclic_weight_total (M : CartanLieCloning.CyclicWeightModel d H) (h : H) :
    (∑ i, M.weight h i) = ∑ i, M.row i := by
  have he := congrArg (fun w : Fin d → ℝ => ∑ i, w i) (M.weight_cone h)
  simp only [Pi.sub_apply, Finset.sum_sub_distrib, WeylCharacter.sum_offset_zero] at he
  exact (sub_eq_zero.mp he).symm

theorem character_coeff (weight : H → Fin d → ℕ) (m : Fin d →₀ ℕ) :
    MvPolynomial.coeff m (character weight) =
      ((Finset.univ.filter (fun h => exponent (weight h) = m)).card : ℂ) := by
  classical
  simp only [character, MvPolynomial.coeff_sum, weightMonomial, MvPolynomial.coeff_monomial]
  simp only [← Nat.cast_sum, ← Finset.sum_boole]

/-- Every nonzero character coefficient comes from an actual basis weight. -/
theorem exists_weight_of_coeff_ne_zero (weight : H → Fin d → ℕ) (m : Fin d →₀ ℕ)
    (hm : MvPolynomial.coeff m (character weight) ≠ 0) :
    ∃ h : H, exponent (weight h) = m := by
  classical
  rw [character_coeff] at hm
  have hc : (Finset.univ.filter (fun h => exponent (weight h) = m)).Nonempty :=
    Finset.card_pos.mp (Nat.pos_of_ne_zero (fun hz => hm (by rw [hz]; simp)))
  obtain ⟨h, hh⟩ := hc
  exact ⟨h, (Finset.mem_filter.mp hh).2⟩

/-- The highest coefficient is exactly one, proved by highest-line uniqueness. -/
theorem cyclic_character_highest_coeff [Nonempty H]
    (M : CartanLieCloning.CyclicWeightModel d H) (weight : H → Fin d → ℕ)
    (hw : ∀ h i, M.weight h i = (weight h i : ℝ))
    (mu : Fin d → ℕ) (hmu : ∀ i, M.row i = (mu i : ℝ)) :
    MvPolynomial.coeff (exponent mu) (character weight) = 1 := by
  classical
  rw [character_coeff]
  have hexp (h : H) : exponent (weight h) = exponent mu ↔ M.weight h = M.row := by
    constructor
    · intro he
      funext i
      have hi := congrArg (fun m : Fin d →₀ ℕ => m i) he
      simpa only [hw, hmu, exponent, Finsupp.coe_equivFunOnFinite_symm] using congrArg (fun n : ℕ => (n : ℝ)) hi
    · intro he
      ext i
      have hi := congrFun he i
      rw [hw, hmu] at hi
      exact_mod_cast hi
  have hf : Finset.univ.filter (fun h => exponent (weight h) = exponent mu) = {M.highestBasis} := by
    ext h
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton, hexp]
    constructor
    · exact fun hh => M.highest_basis_unique h M.highestBasis hh M.highestBasis_weight
    · intro hh
      rw [hh]
      exact M.highestBasis_weight
  rw [hf, Finset.card_singleton]
  norm_num

/-- Every actual nonzero character exponent lies below the highest row in
the integral simple-root cone. -/
theorem cyclic_character_root_cone (M : CartanLieCloning.CyclicWeightModel d H)
    (weight : H → Fin d → ℕ) (hw : ∀ h i, M.weight h i = (weight h i : ℝ))
    (m : Fin d →₀ ℕ) (hm : MvPolynomial.coeff m (character weight) ≠ 0) :
    ∃ c : Fin (d - 1) → ℕ, M.row - (fun i => (m i : ℝ)) = CasimirWeights.offset c := by
  obtain ⟨h, hh⟩ := exists_weight_of_coeff_ne_zero weight m hm
  refine ⟨M.weightCoeff h, ?_⟩
  rw [← hh]
  simpa only [exponent, Finsupp.coe_equivFunOnFinite_symm, ← hw] using M.weight_cone h

end FreeEntropy.LieCharacter
