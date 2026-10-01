/-
Copyright (c) 2026 Free Entropy formalization contributors.
See LICENSE and NOTICE in the repository root for license and attribution.
-/

import FreeEntropy.OccupationCommutant
import FreeEntropy.UnitaryColumn
import FreeEntropy.ScalarCommutantIrreducible
import FreeEntropy.UnitaryHaar

/-!
# Genuine irreducibility of the constructed symmetric power

The group is the actual physical unitary group. Diagonal phases separate
occupation weights, and an explicitly existing unitary with a nonzero column
forces the commutant to be scalar. Orthogonal projections then prove actual
representation irreducibility. No representation-existence premise remains.
-/
noncomputable section
open Matrix
open scoped Matrix.Norms.Elementwise
namespace FreeEntropy.Occupation

/-- The constructed symmetric-power representation of the physical U(d). -/
def unitaryRepresentation (d n : ℕ) : Matrix.unitaryGroup (Fin d) ℂ →*
    Matrix (Occupation d n) (Occupation d n) ℂ :=
  symmetricRepresentation (n := n) (Matrix.unitaryGroup (Fin d) ℂ).subtype

theorem unitaryRepresentation_unitary (d n : ℕ) (U : Matrix.unitaryGroup (Fin d) ℂ) :
    (unitaryRepresentation d n U)ᴴ * unitaryRepresentation d n U = 1 := by
  apply symmetricMatrix_unitary
  exact Matrix.UnitaryGroup.star_mul_self U

theorem unitaryRepresentation_continuous (d n : ℕ) : Continuous (unitaryRepresentation d n) :=
  symmetricMatrix_continuous.comp continuous_subtype_val

/-- The actual finite symmetric-power representation is irreducible. -/
theorem unitaryRepresentation_irreducible (d n : ℕ) (hd : 0 < d) :
    Representation.IsIrreducible (Twirling.matrixRepresentation (unitaryRepresentation d n)) := by
  let i₀ : Fin d := ⟨0, hd⟩
  letI : Nonempty (Occupation d n) := ⟨highestOccupation i₀⟩
  apply Twirling.irreducible_of_scalar_commutant (unitaryRepresentation d n)
    (unitaryRepresentation_unitary d n)
  intro T hT
  obtain ⟨U, hU⟩ := UnitaryColumn.exists_unitary_nonzero_column i₀
  exact commutant_scalar_of_nonzero_column i₀ U hU T (fun W => (hT W).symm)

end FreeEntropy.Occupation
