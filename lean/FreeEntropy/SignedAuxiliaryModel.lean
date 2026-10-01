/-
Copyright (c) 2026 Free Entropy formalization contributors.
See LICENSE and NOTICE in the repository root for license and attribution.
-/

import FreeEntropy.ExteriorWeightCoordinates
import FreeEntropy.CyclicWeightShift

/-! Every dominant integral difference of natural highest rows has an actual
cyclic auxiliary model. A concrete determinant shift handles negative rows. -/
noncomputable section
open scoped BigOperators
namespace FreeEntropy.ExteriorRepresentation
open CartanLieCloning
set_option backward.isDefEq.respectTransparency false
variable {d : ℕ}

def auxiliaryShift (mu : Fin d → ℕ) : ℕ := ∑ i, mu i

theorem le_auxiliaryShift (mu : Fin d → ℕ) (i : Fin d) : mu i ≤ auxiliaryShift mu :=
  Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)

def auxiliaryRow (mu nu : Fin d → ℕ) (i : Fin d) : ℕ :=
  nu i + (auxiliaryShift mu - mu i)

theorem auxiliaryRow_cast (mu nu : Fin d → ℕ) (i : Fin d) :
    (auxiliaryRow mu nu i : ℝ) = (nu i : ℝ) - (mu i : ℝ) + auxiliaryShift mu := by
  rw [auxiliaryRow, Nat.cast_add, Nat.cast_sub (le_auxiliaryShift mu i)]
  ring

theorem auxiliaryRow_antitone (mu nu : Fin d → ℕ)
    (hinc : Antitone (fun i => (nu i : ℝ) - (mu i : ℝ))) : Antitone (auxiliaryRow mu nu) := by
  intro i j hij
  have h : (auxiliaryRow mu nu j : ℝ) ≤ (auxiliaryRow mu nu i : ℝ) := by
    rw [auxiliaryRow_cast, auxiliaryRow_cast]
    linarith [hinc hij]
  exact_mod_cast h

/-- Balancing the polynomial degrees realizes the determinant twist. -/
theorem auxiliaryRow_balance (mu nu : Fin d → ℕ) :
    mu + auxiliaryRow mu nu = nu + fun _ => auxiliaryShift mu := by
  funext i
  simp only [Pi.add_apply, auxiliaryRow]
  have h := Nat.sub_add_cancel (le_auxiliaryShift mu i)
  omega

local instance auxiliaryIndex_nonempty (mu nu : Fin d → ℕ) :
    Nonempty (IrrepIndex (auxiliaryRow mu nu)) :=
  Fin.pos_iff_nonempty.mp (irrep_dimension_pos _)

def canonicalAuxiliaryModel (mu nu : Fin d → ℕ) :
    CyclicWeightModel d (IrrepIndex (auxiliaryRow mu nu)) :=
  (canonicalWeightModel (auxiliaryRow mu nu)).shift (-(auxiliaryShift mu : ℝ))

theorem canonicalAuxiliaryModel_row (mu nu : Fin d → ℕ)
    (hinc : Antitone (fun i => (nu i : ℝ) - (mu i : ℝ))) :
    (canonicalAuxiliaryModel mu nu).row = fun i => (nu i : ℝ) - (mu i : ℝ) := by
  funext i
  change (canonicalWeightModel (auxiliaryRow mu nu)).row i + -(auxiliaryShift mu : ℝ) = _
  rw [canonicalWeightModel_row _ (auxiliaryRow_antitone mu nu hinc)]
  change (auxiliaryRow mu nu i : ℝ) + -(auxiliaryShift mu : ℝ) = _
  rw [auxiliaryRow_cast]
  ring

/-- Exact highest-weight addition for the source, target, and constructed
auxiliary model, including arbitrary negative entries of their difference. -/
theorem canonicalAuxiliaryModel_hrow (mu nu : Fin d → ℕ) (hmu : Antitone mu)
    (hnu : Antitone nu) (hinc : Antitone (fun i => (nu i : ℝ) - (mu i : ℝ))) :
    (canonicalWeightModel nu).row =
      (canonicalWeightModel mu).row + (canonicalAuxiliaryModel mu nu).row := by
  rw [canonicalWeightModel_row mu hmu, canonicalWeightModel_row nu hnu,
    canonicalAuxiliaryModel_row mu nu hinc]
  funext i
  simp only [Pi.add_apply]
  ring

end FreeEntropy.ExteriorRepresentation
