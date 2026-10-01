/-
Copyright (c) 2026 Free Entropy formalization contributors.
See LICENSE and NOTICE in the repository root for license and attribution.
-/

import FreeEntropy.LiePBWDimension
import FreeEntropy.TensorWeightModel

/-! Polynomial dimension bounds for the actual physical tensor sectors,
with every highest-vector and diagonal-weight premise discharged. -/
noncomputable section
open Matrix
open scoped BigOperators
namespace FreeEntropy.SchurWeyl
set_option backward.isDefEq.respectTransparency false
variable {d n : ℕ}

/-- Every actual tensor sector has polynomial matrix dimension. -/
theorem sector_card_le_pbw_polynomial (i : Sector d n) :
    Fintype.card (SectorSpace d n i) ≤ (n * (d - 1) + 1) ^ (d.choose 2) := by
  obtain ⟨_, _, hw, hr, hc⟩ := sectorWeightHighestVector_spec i
  exact LiePBW.card_le_polynomial_of_cyclic (sectorWeightGenerators i)
    (fun b => (sectorWeight i b).val) n (sectorWeightGenerators_diagonal i)
    (fun b => (sectorWeight i b).property) (sectorHighestOccupation i).val
    (sectorWeightHighestVector i) hw hr hc

private theorem bernoulli_nat (n k : ℕ) : n * k + 1 ≤ (n + 1) ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ]
    calc
      _ ≤ (n * k + 1) * (n + 1) := by nlinarith [Nat.zero_le (n * n * k)]
      _ ≤ _ := Nat.mul_le_mul_right _ ih

/-- A convenient pure power of `n+1` for entropy/concentration estimates. -/
theorem sector_card_le_polynomial (i : Sector d n) :
    Fintype.card (SectorSpace d n i) ≤ (n + 1) ^ ((d - 1) * (d.choose 2)) := by
  apply (sector_card_le_pbw_polynomial i).trans
  rw [pow_mul]
  exact Nat.pow_le_pow_left (bernoulli_nat n (d - 1)) _

end FreeEntropy.SchurWeyl
