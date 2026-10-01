/-
Copyright (c) 2026 Free Entropy formalization contributors.
See LICENSE and NOTICE in the repository root for license and attribution.
-/

import FreeEntropy.ConstructedTensorDecomposition
import FreeEntropy.CyclicWeightShift
import FreeEntropy.LieCartanBalance

/-! Actual Cartan embeddings and channels for arbitrary real highest weights.
In particular negative determinant shifts require no positivity assumption
on the auxiliary highest row. -/
noncomputable section
open Matrix
namespace FreeEntropy.CartanLieCloning
set_option backward.isDefEq.respectTransparency false
variable {d : ℕ} {A B C : Type*} [Fintype A] [DecidableEq A]
  [Fintype B] [DecidableEq B] [Fintype C] [DecidableEq C]
  [Nonempty A] [Nonempty B] [Nonempty C]

/-- The highest-sum Cartan isometry exists between the specified actual
models. It is constructed from the complete Lie decomposition and the
proved uniqueness of cyclic modules with a given highest weight. -/
theorem exists_cartan_isometry (M : CyclicWeightModel d A)
    (N : CyclicWeightModel d B) (S : CyclicWeightModel d C)
    (hrow : S.row = M.row + N.row) :
    ∃ J : Matrix (A × B) C ℂ, Jᴴ * J = 1 ∧
      ∀ i j, (M.generators.tensor N.generators).E i j * J = J * S.generators.E i j := by
  let D := constructedTensorDecomposition M N
  let T := D.constituent D.top
  obtain ⟨W, hW, hWW, hWE⟩ := LiePBW.exists_highest_unitary
    T.generators S.generators (fun i => (S.row i : ℂ)) T.highestVector S.highestVector
    T.highestVector_ne_zero S.highestVector_ne_zero
    (by intro i; rw [show S.row = T.row from hrow.trans D.topWeight.symm]; exact T.vector_weight i)
    S.vector_weight T.vector_raise S.vector_raise T.vector_cyclic S.vector_cyclic
  refine ⟨D.embedding D.top * Wᴴ, ?_, ?_⟩
  · rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
    simp only [Matrix.mul_assoc, ← Matrix.mul_assoc (D.embedding D.top)ᴴ (D.embedding D.top),
      D.isometry, Matrix.one_mul, hWW]
  · intro i j
    have ha := congrArg Matrix.conjTranspose (hWE j i)
    simp only [Matrix.conjTranspose_mul, LieMatrixCasimir.Generators.adjoint] at ha
    rw [← Matrix.mul_assoc, D.intertwines, Matrix.mul_assoc, ha, ← Matrix.mul_assoc]

/-- The isometry and exact partial trace normalization are both conclusions. -/
theorem exists_balanced_cartan_isometry (M : CyclicWeightModel d A)
    (N : CyclicWeightModel d B) (S : CyclicWeightModel d C)
    (hrow : S.row = M.row + N.row) :
    ∃ J : Matrix (A × B) C ℂ, Jᴴ * J = 1 ∧
      (∀ i j, (M.generators.tensor N.generators).E i j * J = J * S.generators.E i j) ∧
      CartanChannel.partialTrace (J * Jᴴ) =
        ((Fintype.card C : ℝ) / (Fintype.card A : ℝ)) • (1 : Matrix A A ℂ) := by
  obtain ⟨J, hJ, hJE⟩ := exists_cartan_isometry M N S hrow
  exact ⟨J, hJ, hJE, CartanBalance.balance_of_cyclic_weight M N S J hJ hJE⟩

/-- Arbitrary signed determinant shifts on the auxiliary model are allowed. -/
theorem exists_shifted_cartan_isometry (M : CyclicWeightModel d A)
    (N : CyclicWeightModel d B) (S : CyclicWeightModel d C) (c : ℝ)
    (hrow : ∀ i, S.row i = M.row i + N.row i - c) :
    ∃ J : Matrix (A × B) C ℂ, Jᴴ * J = 1 ∧
      (∀ i j, (M.generators.tensor (N.shift (-c)).generators).E i j * J =
        J * S.generators.E i j) ∧
      CartanChannel.partialTrace (J * Jᴴ) =
        ((Fintype.card C : ℝ) / (Fintype.card A : ℝ)) • (1 : Matrix A A ℂ) := by
  apply exists_balanced_cartan_isometry M (N.shift (-c)) S
  funext i
  simpa only [Pi.add_apply, CyclicWeightModel.shift_row, sub_eq_add_neg, add_assoc] using hrow i

/-- The chosen genuine Cartan inclusion between specified highest models. -/
def canonicalCartanIsometry (M : CyclicWeightModel d A)
    (N : CyclicWeightModel d B) (S : CyclicWeightModel d C)
    (hrow : S.row = M.row + N.row) : Matrix (A × B) C ℂ :=
  (exists_balanced_cartan_isometry M N S hrow).choose

theorem canonicalCartanIsometry_spec (M : CyclicWeightModel d A)
    (N : CyclicWeightModel d B) (S : CyclicWeightModel d C)
    (hrow : S.row = M.row + N.row) :
    (canonicalCartanIsometry M N S hrow)ᴴ * canonicalCartanIsometry M N S hrow = 1 ∧
      (∀ i j, (M.generators.tensor N.generators).E i j * canonicalCartanIsometry M N S hrow =
        canonicalCartanIsometry M N S hrow * S.generators.E i j) ∧
      CartanChannel.partialTrace
        (canonicalCartanIsometry M N S hrow * (canonicalCartanIsometry M N S hrow)ᴴ) =
        ((Fintype.card C : ℝ) / (Fintype.card A : ℝ)) • (1 : Matrix A A ℂ) :=
  (exists_balanced_cartan_isometry M N S hrow).choose_spec

/-- Actual forward CPTP channel, including signed auxiliary models. -/
def canonicalForwardChannel (M : CyclicWeightModel d A)
    (N : CyclicWeightModel d B) (S : CyclicWeightModel d C)
    (hrow : S.row = M.row + N.row) : Channels.MatrixChannel A C :=
  CartanChannel.cartanChannel (canonicalCartanIsometry M N S hrow)
    (Fintype.card A) (Fintype.card C)
    (by exact_mod_cast Fintype.card_pos (α := A))
    (by exact_mod_cast Fintype.card_pos (α := C))
    (canonicalCartanIsometry_spec M N S hrow).2.2

/-- Actual reverse CPTP channel for the same specified target model. -/
def canonicalReverseChannel (M : CyclicWeightModel d A)
    (N : CyclicWeightModel d B) (S : CyclicWeightModel d C)
    (hrow : S.row = M.row + N.row) : Channels.MatrixChannel C A :=
  CartanChannel.reverseChannel (canonicalCartanIsometry M N S hrow)
    (canonicalCartanIsometry_spec M N S hrow).1

end FreeEntropy.CartanLieCloning
