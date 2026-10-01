/-
Copyright (c) 2026 Free Entropy formalization contributors.
See LICENSE and NOTICE in the repository root for license and attribution.
-/

import FreeEntropy.WeylCharacterCone
import Mathlib.Data.Fin.Tuple.Sort

/-! A strictly decreasing nonzero numerator exponent is forced to be the
highest shifted row by the proved Casimir energy and positive-root cone. -/
noncomputable section
open scoped BigOperators
namespace FreeEntropy.WeylCharacter
open MvPolynomial CasimirWeights
set_option backward.isDefEq.respectTransparency false
variable {d : ℕ}

theorem shiftedHighest_cast (mu : Fin d → ℕ) (i : Fin d) :
    (shiftedHighest mu i : ℝ) = (mu i : ℝ) + staircase i := by
  simp only [shiftedHighest, Nat.cast_add, staircase]
  rw [Nat.cast_sub (by omega), Nat.cast_sub (by have := i.isLt; omega)]
  norm_num

theorem strictAnti_exponent_unique (mu m : Fin d → ℕ) (hmu : Antitone mu)
    (hm : StrictAnti m)
    (hc : ∃ c : Fin (d - 1) → ℕ,
      (fun i => (mu i : ℝ) + staircase i) - (fun i => (m i : ℝ)) = offset c)
    (he : (∑ i, m i ^ 2) = ∑ i, shiftedHighest mu i ^ 2) :
    m = shiftedHighest mu := by
  obtain ⟨c, hc⟩ := hc
  let chi : Fin d → ℝ := fun i => (m i : ℝ) - staircase i
  have hcone : (fun i => (mu i : ℝ)) - chi = offset c := by
    convert hc using 1
    funext i
    simp only [chi, Pi.sub_apply]
    ring
  have hdom : ∀ j, chi (right j) ≤ chi (left j) := by
    intro j
    have hj : left j < right j := by change j.val < j.val + 1; omega
    have hmj := hm hj
    have hr : (m (right j) : ℝ) + 1 ≤ m (left j) := by exact_mod_cast hmj
    simp only [chi, staircase, left, right, Nat.cast_add, Nat.cast_one] at hr ⊢
    linarith
  have henergy : shiftedEnergy (fun i => (mu i : ℝ)) = shiftedEnergy chi := by
    have he' : (∑ i, (m i : ℝ) ^ 2) = ∑ i, (shiftedHighest mu i : ℝ) ^ 2 := by exact_mod_cast he
    simp only [shiftedHighest_cast] at he'
    simpa only [shiftedEnergy, chi, sub_add_cancel] using he'.symm
  have heq := dominant_shiftedEnergy_unique (fun i => (mu i : ℝ)) chi c
    (fun j => by
      change (mu (right j) : ℝ) ≤ (mu (left j) : ℝ)
      exact_mod_cast hmu (show left j ≤ right j by change j.val ≤ j.val + 1; omega))
    hdom hcone henergy
  funext i
  have hi := congrFun heq i
  have ht := shiftedHighest_cast mu i
  change (m i : ℝ) - staircase i = (mu i : ℝ) at hi
  exact_mod_cast (show (m i : ℝ) = (shiftedHighest mu i : ℝ) by linarith)

end FreeEntropy.WeylCharacter

namespace FreeEntropy.ExteriorRepresentation
open WeylCharacter
set_option backward.isDefEq.respectTransparency false
variable {d : ℕ}

theorem canonicalCharacter_numerator_below (mu : Fin d → ℕ) (hmu : Antitone mu) :
    Below (fun i => (mu i : ℝ) + staircase i) (denominator d * canonicalCharacter mu) := by
  have hp : Below (fun i => (mu i : ℝ)) (canonicalCharacter mu) :=
    canonicalCharacter_root_cone mu hmu
  convert (below_denominator d).mul hp using 1
  funext i
  simp only [Pi.add_apply]
  ring

theorem canonicalCharacter_strictAnti_exponent (mu : Fin d → ℕ) (hmu : Antitone mu) (hd : 0 < d)
    (m : Fin d →₀ ℕ) (hm : MvPolynomial.coeff m (denominator d * canonicalCharacter mu) ≠ 0)
    (hanti : StrictAnti (fun i => m i)) :
    m = WeylCharacter.exponent (shiftedHighest mu) := by
  have he := strictAnti_exponent_unique mu (fun i => m i) hmu hanti
    (canonicalCharacter_numerator_below mu hmu m hm)
    (canonicalCharacter_numerator_energy mu hmu hd m hm)
  ext i
  exact congrFun he i

end FreeEntropy.ExteriorRepresentation
