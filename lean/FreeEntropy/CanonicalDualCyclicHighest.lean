/-
Copyright (c) 2026 Free Entropy formalization contributors.
See LICENSE and NOTICE in the repository root for license and attribution.
-/

import FreeEntropy.CanonicalDualHighest
import FreeEntropy.LieDualCyclicity

/-! The actual reverse auxiliary is an irreducible highest-weight module,
with its correct dominant reversed negative row and full cyclicity. -/
noncomputable section
open Matrix
namespace FreeEntropy.ExteriorRepresentation
open CartanLieCloning
set_option backward.isDefEq.respectTransparency false
variable {d : ℕ}
local instance dual_cyclic_index_nonempty (mu : Fin d → ℕ) : Nonempty (IrrepIndex mu) :=
  Fin.pos_iff_nonempty.mp (irrep_dimension_pos mu)

/-- Complete highest-weight identification of the contragredient auxiliary
used by the reverse cloning Choi component. -/
theorem canonicalAuxiliary_dual_cyclic_highest (mu nu : Fin d → ℕ)
    (hinc : Antitone (fun i => (nu i : ℝ) - (mu i : ℝ))) :
    ∃ v : IrrepIndex (auxiliaryRow mu nu) → ℂ, v ≠ 0 ∧
    (∀ i, (canonicalAuxiliaryModel mu nu).generators.dual.E i i *ᵥ v =
      ((mu i.rev : ℂ) - (nu i.rev : ℂ)) • v) ∧
    (∀ i j, i < j → (canonicalAuxiliaryModel mu nu).generators.dual.E i j *ᵥ v = 0) ∧
    LiePBW.cyclicSpan (canonicalAuxiliaryModel mu nu).generators.dual v = ⊤ := by
  obtain ⟨v, hv, hw, hr⟩ := canonicalAuxiliary_dual_highest mu nu hinc
  exact ⟨v, hv, hw, hr, (canonicalAuxiliaryModel mu nu).dual_cyclic_of_ne_zero v hv⟩

end FreeEntropy.ExteriorRepresentation
