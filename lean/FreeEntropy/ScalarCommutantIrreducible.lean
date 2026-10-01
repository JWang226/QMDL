/-
Copyright (c) 2026 Free Entropy formalization contributors.
See LICENSE and NOTICE in the repository root for license and attribution.
-/

import FreeEntropy.Twirling
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.Analysis.InnerProductSpace.Adjoint

/-! A unitary finite-dimensional matrix representation with scalar commutant
is genuinely irreducible. The proof constructs the orthogonal projection
onto each invariant subspace and proves that it commutes with the action. -/

noncomputable section
open Matrix
open scoped ComplexInnerProductSpace

namespace FreeEntropy.Twirling

variable {G H : Type*} [Group G] [Fintype H] [DecidableEq H] [Nonempty H]

omit [Nonempty H] in
private theorem euclidean_mul_apply (A B : Matrix H H ℂ) (v : EuclideanSpace ℂ H) :
    Matrix.toEuclideanLin (A * B) v =
      Matrix.toEuclideanLin A (Matrix.toEuclideanLin B v) := by
  simp only [Matrix.toLpLin_apply, Matrix.mulVec_mulVec]

theorem irreducible_of_scalar_commutant (U : G →* Matrix H H ℂ)
    (hunitary : ∀ g, (U g)ᴴ * U g = 1)
    (hscalar : ∀ A : Matrix H H ℂ, (∀ g, U g * A = A * U g) →
      ∃ c : ℂ, A = c • (1 : Matrix H H ℂ)) :
    Representation.IsIrreducible (matrixRepresentation U) := by
  let e := (EuclideanSpace.equiv H ℂ).toLinearEquiv
  haveI : Nontrivial (Subrepresentation (matrixRepresentation U)) := by
    refine ⟨⟨⊥, ⊤, ?_⟩⟩
    intro he
    have h : (⊥ : Submodule ℂ (H → ℂ)) = ⊤ :=
      congrArg Subrepresentation.toSubmodule he
    exact bot_ne_top h
  refine ⟨fun S => ?_⟩
  let K : Submodule ℂ (EuclideanSpace ℂ H) := S.toSubmodule.comap e.toLinearMap
  have hK (g : G) (v : EuclideanSpace ℂ H) (hv : v ∈ K) :
      Matrix.toEuclideanLin (U g) v ∈ K := by
    exact S.apply_mem_toSubmodule g hv
  have hcomm (g : G) (v : EuclideanSpace ℂ H) :
      K.starProjection (Matrix.toEuclideanLin (U g) v) =
        Matrix.toEuclideanLin (U g) (K.starProjection v) := by
    apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero
    · exact hK g _ (K.starProjection_apply_mem v)
    · intro w hw
      rw [← map_sub, ← LinearMap.adjoint_inner_right,
        ← Matrix.toEuclideanLin_conjTranspose_eq_adjoint,
        ← inverse_eq_conjTranspose U hunitary]
      exact K.starProjection_inner_eq_zero v _ (hK g⁻¹ w hw)
  let P : Matrix H H ℂ := Matrix.toEuclideanLin.symm K.starProjection.toLinearMap
  obtain ⟨c, hc⟩ := hscalar P (fun g => by
    apply Matrix.toEuclideanLin.injective
    apply LinearMap.ext
    intro v
    simp only [euclidean_mul_apply, P, LinearEquiv.apply_symm_apply]
    change Matrix.toEuclideanLin (U g) (K.starProjection v) =
      K.starProjection (Matrix.toEuclideanLin (U g) v)
    exact (hcomm g v).symm)
  have hPc (v : EuclideanSpace ℂ H) : K.starProjection v = c • v := by
    have h := congrArg (fun A : Matrix H H ℂ => Matrix.toEuclideanLin A v) hc
    simpa only [P, LinearEquiv.apply_symm_apply, map_smul, LinearMap.smul_apply,
      Matrix.toLpLin_apply, Matrix.one_mulVec, WithLp.toLp_ofLp] using h
  by_cases hc0 : c = 0
  · left
    apply Subrepresentation.toSubmodule_injective
    apply le_antisymm ?_ bot_le
    intro x hx
    change x = 0
    have hp : K.starProjection (e.symm x) = e.symm x :=
      Submodule.starProjection_eq_self_iff.mpr (by simpa [K] using hx)
    rw [hPc, hc0, zero_smul] at hp
    have hzero : e.symm x = 0 := hp.symm
    exact e.symm.injective (by simpa using hzero)
  · right
    apply Subrepresentation.toSubmodule_injective
    apply top_unique
    intro x _
    have hmem : c • e.symm x ∈ K := by
      rw [← hPc]
      exact K.starProjection_apply_mem _
    have hx : e.symm x ∈ K := (Submodule.smul_mem_iff _ hc0).mp hmem
    simpa [K] using hx

end FreeEntropy.Twirling
