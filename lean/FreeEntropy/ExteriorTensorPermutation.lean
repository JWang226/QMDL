/-
Copyright (c) 2026 Free Entropy formalization contributors.
See LICENSE and NOTICE in the repository root for license and attribution.
-/

import FreeEntropy.ExteriorTensor
import Mathlib.LinearAlgebra.Matrix.Permutation

/-! Literal permutation unitaries that rearrange dependent exterior-tensor
factors without changing the representation or its highest basis vector. -/

noncomputable section
open Matrix
open scoped BigOperators
namespace FreeEntropy.ExteriorRepresentation
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false

variable {d k l : ℕ}

def indexCast (h : k = l) : Index d k ≃ Index d l := by
  subst l
  exact Equiv.refl _

@[simp] theorem exteriorMatrix_indexCast (h : k = l) (U : Matrix (Fin d) (Fin d) ℂ)
    (x y : Index d k) :
    exteriorMatrix l U (indexCast h x) (indexCast h y) = exteriorMatrix k U x y := by
  subst l
  rfl

@[simp] theorem indexCast_first (h : k = l) (hk : k ≤ d) (hl : l ≤ d) :
    indexCast h (first hk) = first hl := by subst l; rfl

variable {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    {height : I → ℕ} {height' : J → ℕ}

/-- A height-preserving permutation transports every actual wedge-subset factor. -/
def tensorIndexEquiv (e : I ≃ J) (he : ∀ i, height' (e i) = height i) :
    TensorIndex (d := d) height ≃ TensorIndex (d := d) height' :=
  e.piCongr (fun i => indexCast (he i).symm)

@[simp] theorem tensorIndexEquiv_apply (e : I ≃ J) (he : ∀ i, height' (e i) = height i)
    (x : TensorIndex (d := d) height) (i : I) :
    tensorIndexEquiv e he x (e i) = indexCast (he i).symm (x i) :=
  Equiv.piCongr_apply_apply e _ x i

theorem tensorMatrix_permuted (e : I ≃ J) (he : ∀ i, height' (e i) = height i)
    (U : Matrix (Fin d) (Fin d) ℂ) (x y : TensorIndex (d := d) height) :
    tensorMatrix height' U (tensorIndexEquiv e he x) (tensorIndexEquiv e he y) =
      tensorMatrix height U x y := by
  change (∏ j, exteriorMatrix (height' j) U _ _) = ∏ i, exteriorMatrix (height i) U _ _
  rw [← Equiv.prod_comp e]
  apply Finset.prod_congr rfl
  intro i _
  simp only [tensorIndexEquiv_apply, exteriorMatrix_indexCast]

theorem tensorIndexEquiv_first (e : I ≃ J) (he : ∀ i, height' (e i) = height i)
    (hh : ∀ i, height i ≤ d) (hh' : ∀ j, height' j ≤ d) :
    tensorIndexEquiv e he (tensorFirst height hh) = tensorFirst height' hh' := by
  apply funext
  intro j
  obtain ⟨i, rfl⟩ := e.surjective j
  simp only [tensorIndexEquiv_apply, tensorFirst]
  exact indexCast_first (he i).symm (hh i) (hh' (e i))

section PermutationMatrix
variable {A B : Type*} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]

def basisPermutation (e : A ≃ B) : Matrix B A ℂ := e.symm.toPEquiv.toMatrix

theorem basisPermutation_adjoint (e : A ≃ B) :
    (basisPermutation e)ᴴ = e.toPEquiv.toMatrix := by
  ext i j
  simp [basisPermutation, Matrix.conjTranspose_apply, PEquiv.toMatrix_apply,
    Equiv.eq_symm_apply, eq_comm]

theorem basisPermutation_isometry (e : A ≃ B) :
    (basisPermutation e)ᴴ * basisPermutation e = 1 := by
  rw [basisPermutation_adjoint, basisPermutation, PEquiv.toMatrix_toPEquiv_mul]
  ext i j
  simp [Matrix.submatrix_apply, PEquiv.toMatrix_apply, Matrix.one_apply]

theorem basisPermutation_coisometry (e : A ≃ B) :
    basisPermutation e * (basisPermutation e)ᴴ = 1 := by
  rw [basisPermutation_adjoint, basisPermutation, PEquiv.toMatrix_toPEquiv_mul]
  ext i j
  simp [Matrix.submatrix_apply, PEquiv.toMatrix_apply, Matrix.one_apply]

theorem basisPermutation_mulVec (e : A ≃ B) (v : A → ℂ) :
    basisPermutation e *ᵥ v = v ∘ e.symm :=
  PEquiv.toMatrix_toPEquiv_mulVec e.symm v

theorem basisPermutation_single (e : A ≃ B) (a : A) (c : ℂ) :
    basisPermutation e *ᵥ Pi.single a c = Pi.single (e a) c := by
  rw [basisPermutation_mulVec]
  funext b
  by_cases hb : b = e a
  · subst b
    change (Pi.single a c : A → ℂ) (e.symm (e a)) = (Pi.single (e a) c : B → ℂ) (e a)
    rw [e.symm_apply_apply]
    simp
  · have ha : e.symm b ≠ a := by
      intro h
      exact hb ((e.apply_symm_apply b).symm.trans (congrArg e h))
    simp [hb, ha]

theorem basisPermutation_intertwines (e : A ≃ B) (M : Matrix A A ℂ) (N : Matrix B B ℂ)
    (he : ∀ a b, N (e a) (e b) = M a b) :
    N * basisPermutation e = basisPermutation e * M := by
  rw [basisPermutation, PEquiv.mul_toMatrix_toPEquiv, PEquiv.toMatrix_toPEquiv_mul]
  ext i j
  simpa only [Matrix.submatrix_apply, Equiv.symm_symm, id_eq, Equiv.apply_symm_apply] using
    he (e.symm i) j

end PermutationMatrix

/-- The actual unitary between differently ordered exterior tensor products. -/
def tensorPermutation (e : I ≃ J) (he : ∀ i, height' (e i) = height i) :
    Matrix (TensorIndex (d := d) height') (TensorIndex (d := d) height) ℂ :=
  basisPermutation (tensorIndexEquiv e he)

theorem tensorPermutation_isometry (e : I ≃ J) (he : ∀ i, height' (e i) = height i) :
    (tensorPermutation (d := d) e he)ᴴ * tensorPermutation (d := d) e he = 1 :=
  basisPermutation_isometry _

theorem tensorPermutation_coisometry (e : I ≃ J) (he : ∀ i, height' (e i) = height i) :
    tensorPermutation (d := d) e he * (tensorPermutation (d := d) e he)ᴴ = 1 :=
  basisPermutation_coisometry _

theorem tensorPermutation_intertwines (e : I ≃ J) (he : ∀ i, height' (e i) = height i)
    (U : Matrix (Fin d) (Fin d) ℂ) :
    tensorMatrix height' U * tensorPermutation e he = tensorPermutation e he * tensorMatrix height U :=
  basisPermutation_intertwines _ _ _ (tensorMatrix_permuted e he U)

/-- Rearrangement sends the highest basis vector exactly to the highest
basis vector, with no phase or normalization ambiguity. -/
theorem tensorPermutation_highest (e : I ≃ J) (he : ∀ i, height' (e i) = height i)
    (hh : ∀ i, height i ≤ d) (hh' : ∀ j, height' j ≤ d) :
    tensorPermutation e he *ᵥ Pi.single (tensorFirst height hh) 1 =
      Pi.single (tensorFirst height' hh') 1 := by
  change basisPermutation (tensorIndexEquiv e he) *ᵥ _ = _
  rw [basisPermutation_single, tensorIndexEquiv_first e he hh hh']

end FreeEntropy.ExteriorRepresentation

