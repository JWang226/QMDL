/-
Copyright (c) 2026 Free Entropy formalization contributors.
See LICENSE and NOTICE in the repository root for license and attribution.
-/

import FreeEntropy.LiePBWMultiplicity

/-! The dimension of a literal diagonal weight space is its actual finite
coordinate multiplicity. -/
noncomputable section
namespace FreeEntropy.LiePBW
variable {d : ℕ} {H : Type*} [Fintype H] [DecidableEq H]
set_option backward.isDefEq.respectTransparency false

def coordinateWeightSpaceEquiv (wt : H → Fin d → ℂ) (target : Fin d → ℂ) :
    coordinateWeightSpace wt target ≃ₗ[ℂ] ({h : H // wt h = target} → ℂ) := by
  classical
  exact
    { toFun := fun x h => x.val h.val
      invFun := fun y => ⟨fun h => if hh : wt h = target then y ⟨h, hh⟩ else 0,
        fun h hh => by simp only [dif_neg hh]⟩
      left_inv := by
        intro x
        apply Subtype.ext
        funext h
        dsimp
        split_ifs with hh
        · rfl
        · exact (x.property h hh).symm
      right_inv := by intro y; funext h; simp [h.property]
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }

theorem coordinateWeightSpace_finrank (wt : H → Fin d → ℂ) (target : Fin d → ℂ) :
    Module.finrank ℂ (coordinateWeightSpace wt target) =
      Fintype.card {h : H // wt h = target} := by
  classical
  calc
    _ = Module.finrank ℂ ({h : H // wt h = target} → ℂ) := (coordinateWeightSpaceEquiv wt target).finrank_eq
    _ = _ := by simp

end FreeEntropy.LiePBW
