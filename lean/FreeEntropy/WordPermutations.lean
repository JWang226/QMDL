/-
Copyright (c) 2026 Free Entropy formalization contributors.
See LICENSE and NOTICE in the repository root for license and attribution.
-/

import FreeEntropy.WordTypes
import FreeEntropy.TensorPowers

/-! Words with equal content differ by a permutation of tensor positions.
Consequently genuine tensor-power matrices preserve the occupation subspace. -/
noncomputable section
open scoped BigOperators
open Matrix
namespace FreeEntropy.WordTypes
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
variable {n d : ℕ}

/-- The bijection matching each letter's positions in two equal-content words. -/
def positionEquiv (x y : Fin n → Fin d) (h : content x = content y) : Equiv.Perm (Fin n) :=
  (Equiv.sigmaFiberEquiv x).symm.trans
    ((Equiv.sigmaCongrRight (fun i => Fintype.equivOfCardEq (show
      Fintype.card {t // x t = i} = Fintype.card {t // y t = i} from by
        simpa [Fintype.card_subtype, content] using congrFun h i))).trans
      (Equiv.sigmaFiberEquiv y))

theorem positionEquiv_apply (x y : Fin n → Fin d) (h : content x = content y) (t : Fin n) :
    y (positionEquiv x y h t) = x t := by
  exact ((Fintype.equivOfCardEq (show Fintype.card {s // x s = x t} =
    Fintype.card {s // y s = x t} from by
      simpa [Fintype.card_subtype, content] using congrFun h (x t))) ⟨t, rfl⟩).property

/-- Precomposition permutes the whole word space. -/
def permuteWords (e : Equiv.Perm (Fin n)) : Equiv.Perm (Fin n → Fin d) where
  toFun w := w ∘ e
  invFun w := w ∘ e.symm
  left_inv w := by funext t; simp
  right_inv w := by funext t; simp

theorem content_permute (w : Fin n → Fin d) (e : Equiv.Perm (Fin n)) :
    content (permuteWords e w) = content w := by
  funext i
  have h := Equiv.sum_comp e (fun t => if w t = i then (1 : ℕ) else 0)
  simpa [content, permuteWords] using h

/-- The symmetric tensor space consists exactly of amplitudes constant on
word-content classes. -/
def ContentInvariant (v : (Fin n → Fin d) → ℂ) : Prop :=
  ∀ x y, content x = content y → v x = v y

theorem ContentInvariant.permute {v : (Fin n → Fin d) → ℂ} (hv : ContentInvariant v)
    (w : Fin n → Fin d) (e : Equiv.Perm (Fin n)) : v (permuteWords e w) = v w :=
  hv _ _ (content_permute w e)

theorem tensor_entry_permute (A : Matrix (Fin d) (Fin d) ℂ)
    (x y : Fin n → Fin d) (e : Equiv.Perm (Fin n)) :
    TensorPowers.matrix n A (permuteWords e x) (permuteWords e y) =
      TensorPowers.matrix n A x y := by
  exact Equiv.prod_comp e (fun t => A (x t) (y t))

/-- Every tensor power preserves the actual occupation subspace, without
assuming a representation or a Schur decomposition. -/
theorem ContentInvariant.tensor_action {v : (Fin n → Fin d) → ℂ}
    (hv : ContentInvariant v) (A : Matrix (Fin d) (Fin d) ℂ) :
    ContentInvariant (TensorPowers.matrix n A *ᵥ v) := by
  intro x y hxy
  let e := positionEquiv x y hxy
  have hxe : permuteWords e y = x := by
    funext t
    exact positionEquiv_apply x y hxy t
  rw [← hxe]
  simp only [Matrix.mulVec, dotProduct]
  rw [← Equiv.sum_comp (permuteWords e) (fun z =>
    TensorPowers.matrix n A (permuteWords e y) z * v z)]
  apply Finset.sum_congr rfl
  intro z _
  rw [tensor_entry_permute, hv.permute]

theorem tensor_vector_contentInvariant (v : Fin d → ℂ) :
    ContentInvariant (TensorPowers.vector n v) := by
  intro x y hxy
  have hx : (∏ t, v (x t)) = ∏ i, v i ^ content x i := by
    simpa only [content, Finset.prod_const] using
      (Finset.prod_fiberwise' Finset.univ x v).symm
  have hy : (∏ t, v (y t)) = ∏ i, v i ^ content y i := by
    simpa only [content, Finset.prod_const] using
      (Finset.prod_fiberwise' Finset.univ y v).symm
  exact hx.trans ((congrArg (fun c : Fin d → ℕ => ∏ i, v i ^ c i) hxy).trans hy.symm)

end FreeEntropy.WordTypes
