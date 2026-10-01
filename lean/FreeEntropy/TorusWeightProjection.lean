/-
Copyright (c) 2026 Free Entropy formalization contributors.
See LICENSE and NOTICE in the repository root for license and attribution.
-/

import FreeEntropy.TorusWeightEigenline
import FreeEntropy.UnitaryDecompositionMatrices

/-! Actual weight projections preserve every unitary invariant subspace with
a diagonal integral torus action. This permits polynomial orbit calculations
inside individual weight spaces. -/
noncomputable section
open Matrix
namespace FreeEntropy.TorusWeights
open UnitaryDecomposition
set_option backward.isDefEq.respectTransparency false
variable {I B G : Type*} [Fintype I] [DecidableEq I]
  [Fintype B] [DecidableEq B] [Group G]

def projector (weight : B → I → ℕ) (a : I → ℕ) : Matrix B B ℂ := by
  classical
  exact diagonal (fun b => if weight b = a then 1 else 0)

theorem commutes_projector (weight : B → I → ℕ) (a : I → ℕ) (T : Matrix B B ℂ)
    (hT : ∀ z : I → ℂ, (∀ i, ‖z i‖ = 1) →
      T * diagonal (fun b => character z (weight b)) =
        diagonal (fun b => character z (weight b)) * T) :
    T * projector weight a = projector weight a * T := by
  classical
  have hoff (b c : B) (hbc : weight b ≠ weight c) : T b c = 0 := by
    obtain ⟨z, hz, hchar⟩ := character_separates (weight b) (weight c) hbc
    have he := congrArg (fun M : Matrix B B ℂ => M b c) (hT z hz)
    simp only [Matrix.mul_diagonal, Matrix.diagonal_mul] at he
    have hp : T b c * (character z (weight c) - character z (weight b)) = 0 := by
      rw [mul_sub, he, mul_comm (character z (weight b)), sub_self]
    exact (mul_eq_zero.mp hp).resolve_right (sub_ne_zero.mpr hchar.symm)
  ext b c
  simp only [projector, Matrix.mul_diagonal, Matrix.diagonal_mul]
  by_cases hbc : weight b = weight c
  · rw [hbc]; split_ifs <;> simp
  · rw [hoff b c hbc, zero_mul, mul_zero]

theorem invariant_projection_commutes (U : G →* Matrix B B ℂ)
    (hU : ∀ g, (U g)ᴴ * U g = 1) (K : Subspace B)
    (hK : Invariant (euclideanRepresentation U) K) (g : G) :
    (embedding K * (embedding K)ᴴ) * U g = U g * (embedding K * (embedding K)ᴴ) := by
  apply Matrix.toEuclideanLin.injective
  apply LinearMap.ext
  intro v
  have hmul (A C : Matrix B B ℂ) (x : EuclideanSpace ℂ B) :
      Matrix.toEuclideanLin (A * C) x = Matrix.toEuclideanLin A (Matrix.toEuclideanLin C x) := by
    simp only [Matrix.toLpLin_apply, Matrix.mulVec_mulVec]
  rw [hmul, hmul]
  change Matrix.toEuclideanLin (embedding K * (embedding K)ᴴ)
      (Matrix.toEuclideanLin (U g) v) =
    Matrix.toEuclideanLin (U g) (Matrix.toEuclideanLin (embedding K * (embedding K)ᴴ) v)
  simp only [embedding_projection]
  exact projection_commutes (euclideanRepresentation U) (euclideanRepresentation_adjoint U hU) hK g v

theorem projector_mem (U : G →* Matrix B B ℂ) (hU : ∀ g, (U g)ᴴ * U g = 1)
    (torus : (z : I → ℂ) → (∀ i, ‖z i‖ = 1) → G) (weight : B → I → ℕ)
    (hdiag : ∀ z hz, U (torus z hz) = diagonal (fun b => character z (weight b)))
    (K : Subspace B) (hK : Invariant (euclideanRepresentation U) K)
    (a : I → ℕ) (v : EuclideanSpace ℂ B) (hv : v ∈ K) :
    Matrix.toEuclideanLin (projector weight a) v ∈ K := by
  let P := embedding K * (embedding K)ᴴ
  have hcomm : P * projector weight a = projector weight a * P := by
    apply commutes_projector
    intro z hz
    simpa only [hdiag] using invariant_projection_commutes U hU K hK (torus z hz)
  have hvfix : P *ᵥ v.ofLp = v.ofLp := by
    have h := embedding_projection K v
    rw [Submodule.starProjection_eq_self_iff.mpr hv] at h
    exact congrArg WithLp.ofLp h
  let w := Matrix.toEuclideanLin (projector weight a) v
  have hwfix : Matrix.toEuclideanLin P w = w := by
    apply WithLp.ofLp_injective 2
    change P *ᵥ (projector weight a *ᵥ v.ofLp) = projector weight a *ᵥ v.ofLp
    rw [Matrix.mulVec_mulVec, hcomm, ← Matrix.mulVec_mulVec, hvfix]
  have hp := embedding_projection K w
  rw [hwfix] at hp
  change w ∈ K
  rw [hp]
  exact K.starProjection_apply_mem w

/-- The literal coordinate weight space. -/
def weightSpace (weight : B → I → ℕ) (a : I → ℕ) : Subspace B where
  carrier := {v | ∀ b, weight b ≠ a → v b = 0}
  zero_mem' := by simp
  add_mem' := by intro x y hx hy b hb; simp [hx b hb, hy b hb]
  smul_mem' := by intro c x hx b hb; simp [hx b hb]

theorem projector_mem_weightSpace (weight : B → I → ℕ) (a : I → ℕ)
    (v : EuclideanSpace ℂ B) :
    Matrix.toEuclideanLin (projector weight a) v ∈ weightSpace weight a := by
  classical
  intro b hb
  simp [projector, Matrix.toLpLin_apply, Matrix.mulVec_diagonal, hb]

end FreeEntropy.TorusWeights
