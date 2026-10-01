/-
Copyright (c) 2026 Free Entropy formalization contributors.
See LICENSE and NOTICE in the repository root for license and attribution.
-/

import FreeEntropy.LieCyclicMaps
import Mathlib.Data.Matrix.Block

/-! The actual block direct sum of two star-compatible gl(d) actions. -/
noncomputable section
open Matrix
namespace FreeEntropy.LiePBW
open LieMatrixCasimir
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
variable {d : ℕ} {H K : Type*} [Fintype H] [DecidableEq H] [Fintype K] [DecidableEq K]

def directSum (R : Generators d H) (S : Generators d K) : Generators d (H ⊕ K) where
  E i j := Matrix.fromBlocks (R.E i j) 0 0 (S.E i j)
  adjoint i j := by simp [Matrix.fromBlocks_conjTranspose, R.adjoint, S.adjoint]
  commutator i j k l := by
    have hr := R.commutator i j k l
    have hs := S.commutator i j k l
    by_cases hjk : j = k <;> by_cases hli : l = i <;>
      simp only [hjk, hli, if_true, if_false] at hr hs ⊢ <;>
      simp only [Matrix.fromBlocks_multiply, Matrix.mul_zero, Matrix.zero_mul,
        add_zero, zero_add] <;>
      ext a b
    all_goals
      rcases a with a | a <;> rcases b with b | b
      · simpa only [Matrix.sub_apply, Matrix.fromBlocks_apply₁₁, Matrix.zero_apply] using
          congrArg (fun M : Matrix H H ℂ => M a b) hr
      · simp
      · simp
      · simpa only [Matrix.sub_apply, Matrix.fromBlocks_apply₂₂, Matrix.zero_apply] using
          congrArg (fun M : Matrix K K ℂ => M a b) hs

def firstCoordinate : ((H ⊕ K) → ℂ) →ₗ[ℂ] (H → ℂ) :=
  LinearMap.pi (fun h => LinearMap.proj (Sum.inl h))

def secondCoordinate : ((H ⊕ K) → ℂ) →ₗ[ℂ] (K → ℂ) :=
  LinearMap.pi (fun k => LinearMap.proj (Sum.inr k))

@[simp] theorem firstCoordinate_apply (x : H ⊕ K → ℂ) : firstCoordinate x = x ∘ Sum.inl := rfl
@[simp] theorem secondCoordinate_apply (x : H ⊕ K → ℂ) : secondCoordinate x = x ∘ Sum.inr := rfl

@[simp] theorem directSum_mulVec (R : Generators d H) (S : Generators d K)
    (i j : Fin d) (x : H ⊕ K → ℂ) :
    (directSum R S).E i j *ᵥ x =
      Sum.elim (R.E i j *ᵥ (x ∘ Sum.inl)) (S.E i j *ᵥ (x ∘ Sum.inr)) := by
  simp [directSum, Matrix.fromBlocks_mulVec]

theorem firstCoordinate_intertwines (R : Generators d H) (S : Generators d K)
    (i j : Fin d) (x : H ⊕ K → ℂ) :
    firstCoordinate ((directSum R S).E i j *ᵥ x) = R.E i j *ᵥ firstCoordinate x := by
  rw [directSum_mulVec]
  rfl

theorem secondCoordinate_intertwines (R : Generators d H) (S : Generators d K)
    (i j : Fin d) (x : H ⊕ K → ℂ) :
    secondCoordinate ((directSum R S).E i j *ᵥ x) = S.E i j *ᵥ secondCoordinate x := by
  rw [directSum_mulVec]
  rfl

theorem directSum_weight (R : Generators d H) (S : Generators d K) (lam : Fin d → ℂ)
    (v : H → ℂ) (w : K → ℂ)
    (hv : ∀ i, R.E i i *ᵥ v = lam i • v) (hw : ∀ i, S.E i i *ᵥ w = lam i • w)
    (i : Fin d) : (directSum R S).E i i *ᵥ Sum.elim v w = lam i • Sum.elim v w := by
  rw [directSum_mulVec]
  change Sum.elim (R.E i i *ᵥ v) (S.E i i *ᵥ w) = _
  rw [hv, hw]
  funext x
  cases x <;> rfl

theorem directSum_raise (R : Generators d H) (S : Generators d K)
    (v : H → ℂ) (w : K → ℂ)
    (hv : ∀ i j, i < j → R.E i j *ᵥ v = 0)
    (hw : ∀ i j, i < j → S.E i j *ᵥ w = 0) (i j : Fin d) (hij : i < j) :
    (directSum R S).E i j *ᵥ Sum.elim v w = 0 := by
  rw [directSum_mulVec]
  change Sum.elim (R.E i j *ᵥ v) (S.E i j *ᵥ w) = _
  rw [hv i j hij, hw i j hij]
  funext x
  cases x <;> rfl

end FreeEntropy.LiePBW
