/-
Copyright (c) 2026 Free Entropy formalization contributors.
See LICENSE and NOTICE in the repository root for license and attribution.
-/

import FreeEntropy.UnitaryDecompositionMatrices

/-! Actual unitary changes of coordinates preserve a matrix representation
and its irreducibility. -/
noncomputable section
open Matrix
open scoped Matrix.Norms.Elementwise
namespace FreeEntropy.UnitaryCoordinates
set_option backward.isDefEq.respectTransparency false
variable {G A : Type*} [Group G] [Fintype A] [DecidableEq A]

def representation (U : G →* Matrix A A ℂ) (W : Matrix A A ℂ) (hW : Wᴴ * W = 1) :
    G →* Matrix A A ℂ where
  toFun g := Wᴴ * U g * W
  map_one' := by simp [hW]
  map_mul' g h := by
    simp only [map_mul, Matrix.mul_assoc, ← Matrix.mul_assoc W Wᴴ,
      mul_eq_one_comm.mp hW, Matrix.one_mul]

theorem intertwines (U : G →* Matrix A A ℂ) (W : Matrix A A ℂ) (hW : Wᴴ * W = 1) (g : G) :
    W * representation U W hW g = U g * W := by
  change W * (Wᴴ * U g * W) = _
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, mul_eq_one_comm.mp hW, Matrix.one_mul]

theorem unitary (U : G →* Matrix A A ℂ) (W : Matrix A A ℂ) (hW : Wᴴ * W = 1)
    (hU : ∀ g, (U g)ᴴ * U g = 1) (g : G) :
    (representation U W hW g)ᴴ * representation U W hW g = 1 := by
  change (Wᴴ * U g * W)ᴴ * (Wᴴ * U g * W) = 1
  simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
    Matrix.mul_assoc, ← Matrix.mul_assoc W Wᴴ, mul_eq_one_comm.mp hW,
    Matrix.one_mul, ← Matrix.mul_assoc (U g)ᴴ (U g), hU, Matrix.one_mul, hW]

theorem continuous [TopologicalSpace G] (U : G →* Matrix A A ℂ) (W : Matrix A A ℂ)
    (hW : Wᴴ * W = 1) (hU : Continuous U) : Continuous (representation U W hW) :=
  (continuous_const.matrix_mul hU).matrix_mul continuous_const

def coordinateIntertwiner (U : G →* Matrix A A ℂ) (W : Matrix A A ℂ) (hW : Wᴴ * W = 1) :
    Representation.IntertwiningMap (Twirling.matrixRepresentation (representation U W hW))
      (Twirling.matrixRepresentation U) where
  toLinearMap := Matrix.toLin' W
  isIntertwining' g := by
    apply LinearMap.ext
    intro x
    funext a
    change (W *ᵥ (representation U W hW g *ᵥ x)) a = (U g *ᵥ (W *ᵥ x)) a
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, intertwines]

theorem coordinateIntertwiner_bijective (U : G →* Matrix A A ℂ)
    (W : Matrix A A ℂ) (hW : Wᴴ * W = 1) :
    Function.Bijective (coordinateIntertwiner U W hW) := by
  constructor
  · intro x y h
    have he := congrArg (fun v => Wᴴ *ᵥ v) h
    change Wᴴ *ᵥ (W *ᵥ x) = Wᴴ *ᵥ (W *ᵥ y) at he
    simpa only [Matrix.mulVec_mulVec, hW, Matrix.one_mulVec] using he
  · intro x
    refine ⟨Wᴴ *ᵥ x, ?_⟩
    change W *ᵥ (Wᴴ *ᵥ x) = x
    rw [Matrix.mulVec_mulVec, mul_eq_one_comm.mp hW, Matrix.one_mulVec]

theorem irreducible (U : G →* Matrix A A ℂ) (W : Matrix A A ℂ) (hW : Wᴴ * W = 1)
    (hU : Representation.IsIrreducible (Twirling.matrixRepresentation U)) :
    Representation.IsIrreducible (Twirling.matrixRepresentation (representation U W hW)) := by
  let f := coordinateIntertwiner U W hW
  let l := Representation.IntertwiningMap.equivLinearMapAsModule _ _ f
  have hb : Function.Bijective l := coordinateIntertwiner_bijective U W hW
  apply (Representation.irreducible_iff_isSimpleModule_asModule _).mpr
  apply (LinearMap.isSimpleModule_iff_of_bijective l hb).mpr
  exact (Representation.irreducible_iff_isSimpleModule_asModule _).mp hU

end FreeEntropy.UnitaryCoordinates
