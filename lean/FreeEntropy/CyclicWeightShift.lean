/-
Copyright (c) 2026 Free Entropy formalization contributors.
See LICENSE and NOTICE in the repository root for license and attribution.
-/

import FreeEntropy.LieDeterminantTwist
import FreeEntropy.CyclicWeightHighest
import FreeEntropy.TensorWeightCoordinates

/-! Determinant shifts preserve every structural property of an actual
cyclic weight model, including its root offsets and weight projectors. -/
noncomputable section
open Matrix
namespace FreeEntropy.CartanLieCloning
open LieMatrixCasimir
set_option backward.isDefEq.respectTransparency false
variable {d : ℕ} {A : Type*} [Fintype A] [DecidableEq A]

def CyclicWeightModel.shift (M : CyclicWeightModel d A) (c : ℝ) : CyclicWeightModel d A where
  generators := M.generators.shift c
  row := fun j => M.row j + c
  weight := fun a j => M.weight a j + c
  highest := M.highest
  diagonal j := by
    rw [M.generators.shift_diagonal, M.diagonal]
    ext a b
    by_cases hab : a = b
    · subst b; simp [WeightSectors.weightDiagonal, Complex.ofReal_add]
    · simp [WeightSectors.weightDiagonal, Matrix.diagonal_apply_ne _ hab, Matrix.one_apply_ne hab]
  highest_weight j := by
    rw [M.generators.shift_diagonal, Matrix.add_mul, M.highest_weight,
      Matrix.smul_mul, Matrix.one_mul, add_smul]
  highest_raise i j hij := by
    rw [M.generators.shift_offdiagonal c i j (ne_of_lt hij), M.highest_raise i j hij]
  cyclic := by
    have hc : LiePBW.cyclicSpan (M.generators.shift c) M.highestVector = ⊤ := by
      rw [M.generators.shift_cyclicSpan c (fun j => (M.row j : ℂ)) M.highestVector
        M.vector_weight M.vector_raise, M.vector_cyclic]
    exact (M.generators.shift c).column_cyclic_of_vector M.highestVector hc
  dominant j := by have := M.dominant j; linarith
  weightCoeff := M.weightCoeff
  weight_cone a := by
    convert M.weight_cone a using 1
    funext j
    simp only [Pi.sub_apply]
    ring

@[simp] theorem CyclicWeightModel.shift_row (M : CyclicWeightModel d A) (c : ℝ) (j : Fin d) :
    (M.shift c).row j = M.row j + c := rfl

@[simp] theorem CyclicWeightModel.shift_weight (M : CyclicWeightModel d A) (c : ℝ) (a : A) (j : Fin d) :
    (M.shift c).weight a j = M.weight a j + c := rfl

@[simp] theorem CyclicWeightModel.shift_weightCoeff (M : CyclicWeightModel d A) (c : ℝ) :
    (M.shift c).weightCoeff = M.weightCoeff := rfl

/-- The actual offset weight projector is exactly unchanged by a twist. -/
theorem CyclicWeightModel.shift_weightProjector (M : CyclicWeightModel d A) (c : ℝ)
    (delta : Fin d → ℝ) :
    WeightSectors.weightProjector (M.shift c).weight ((M.shift c).row - delta) =
      WeightSectors.weightProjector M.weight (M.row - delta) := by
  have he (a : A) : (M.shift c).weight a = (M.shift c).row - delta ↔
      M.weight a = M.row - delta := by
    simp only [funext_iff, Pi.sub_apply, CyclicWeightModel.shift_weight,
      CyclicWeightModel.shift_row]
    constructor <;> intro h j <;> have := h j <;> linarith
  unfold WeightSectors.weightProjector
  simp only [he]
  congr 1
  funext a
  by_cases ha : M.weight a = M.row - delta <;> simp only [ha, if_true, if_false]

/-- Shifting cannot change the offset coefficients, hence every normalized
spectral law specified by those coefficients is literally the same. -/
theorem CyclicWeightModel.shift_offset_law (M : CyclicWeightModel d A) (c : ℝ)
    (f : (Fin (d - 1) → ℕ) → ℝ) :
    (fun a => f ((M.shift c).weightCoeff a)) = fun a => f (M.weightCoeff a) := rfl

end FreeEntropy.CartanLieCloning
