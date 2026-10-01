/-
Copyright (c) 2026 Free Entropy formalization contributors.
See LICENSE and NOTICE in the repository root for license and attribution.
-/

import FreeEntropy.TensorLieCyclicity
import FreeEntropy.TensorLieRestriction
import FreeEntropy.LiePBWHighest
import FreeEntropy.UnitaryDecompositionBasic

/-! Actual Lie-invariant subspaces are group-invariant, and every nonzero
vector in an irreducible tensor summand is Lie-cyclic. -/
noncomputable section
open Matrix
open scoped ComplexInnerProductSpace

namespace FreeEntropy.SchurWeyl
set_option backward.isDefEq.respectTransparency false
variable {d n : ℕ} {A : Type*} [Fintype A] [DecidableEq A]

/-- A commutant of the compressed physical generators lifts to the actual
physical commutant, and therefore commutes with the genuine summand action. -/
theorem restricted_commutant_of_generators
    (R : Matrix.unitaryGroup (Fin d) ℂ →* Matrix A A ℂ)
    (J : Matrix (Fin n → Fin d) A ℂ) (hJ : Jᴴ * J = 1)
    (hJR : ∀ U, physicalRepresentation d n U * J = J * R U)
    (T : Matrix A A ℂ)
    (hT : ∀ i j, T * (restrictedGenerators R J hJ hJR).E i j =
      (restrictedGenerators R J hJ hJR).E i j * T) (U : Matrix.unitaryGroup (Fin d) ℂ) :
    T * R U = R U * T := by
  let E := TensorPowers.generators d n
  let F := restrictedGenerators R J hJ hJR
  have hE (i j : Fin d) : E.E i j * J = J * F.E i j :=
    restrictedGenerators_intertwines R J hJ hJR i j
  have hstar (i j : Fin d) : Jᴴ * E.E i j = F.E i j * Jᴴ := by
    have h := congrArg Matrix.conjTranspose (hE j i)
    simpa only [Matrix.conjTranspose_mul, E.adjoint, F.adjoint] using h
  have hLift : TensorCommutant (J * T * Jᴴ) := by
    apply (tensorCommutant_iff_generators _).mpr
    intro i j
    change J * T * Jᴴ * E.E i j = E.E i j * (J * T * Jᴴ)
    calc
      _ = J * (T * F.E i j) * Jᴴ := by rw [Matrix.mul_assoc, hstar]; simp only [Matrix.mul_assoc]
      _ = J * (F.E i j * T) * Jᴴ := by rw [hT]
      _ = _ := by rw [← Matrix.mul_assoc J (F.E i j), ← hE]; simp only [Matrix.mul_assoc]
  have h := congrArg (fun X => Jᴴ * X * J) (hLift U)
  have hadj := intertwiner_adjoint R J hJ hJR U
  change Jᴴ * (J * T * Jᴴ * physicalRepresentation d n U) * J =
    Jᴴ * (physicalRepresentation d n U * (J * T * Jᴴ)) * J at h
  simpa only [Matrix.mul_assoc, hJR, ← Matrix.mul_assoc Jᴴ J, hJ,
    Matrix.one_mul, Matrix.mul_one, ← Matrix.mul_assoc Jᴴ (physicalRepresentation d n U),
    hadj] using h

private theorem invariant_of_commutant_bridge {G H : Type*} [Group G]
    [Fintype H] [DecidableEq H]
    (U : G →* Matrix H H ℂ) (E : LieMatrixCasimir.Generators d H)
    (hbridge : ∀ T : Matrix H H ℂ,
      (∀ i j, T * E.E i j = E.E i j * T) → ∀ g, T * U g = U g * T)
    (S : Submodule ℂ (H → ℂ))
    (hS : ∀ i j x, x ∈ S → E.E i j *ᵥ x ∈ S) :
    ∀ g x, x ∈ S → U g *ᵥ x ∈ S := by
  let e := (EuclideanSpace.equiv H ℂ).toLinearEquiv
  let K : Submodule ℂ (EuclideanSpace ℂ H) := S.comap e.toLinearMap
  have hK (i j : Fin d) (v : EuclideanSpace ℂ H) (hv : v ∈ K) :
      Matrix.toEuclideanLin (E.E i j) v ∈ K := hS i j v.ofLp hv
  have hcomm (i j : Fin d) (v : EuclideanSpace ℂ H) :
      K.starProjection (Matrix.toEuclideanLin (E.E i j) v) =
        Matrix.toEuclideanLin (E.E i j) (K.starProjection v) := by
    apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero
    · exact hK i j _ (K.starProjection_apply_mem v)
    · intro w hw
      rw [← map_sub, ← LinearMap.adjoint_inner_right,
        ← Matrix.toEuclideanLin_conjTranspose_eq_adjoint, E.adjoint]
      exact K.starProjection_inner_eq_zero v _ (hK j i w hw)
  let P : Matrix H H ℂ := Matrix.toEuclideanLin.symm K.starProjection.toLinearMap
  have hP (g : G) : P * U g = U g * P := hbridge P (fun i j => by
    apply Matrix.toEuclideanLin.injective
    apply LinearMap.ext
    intro v
    simp only [Matrix.toLpLin_apply, ← Matrix.mulVec_mulVec]
    change Matrix.toEuclideanLin P (Matrix.toEuclideanLin (E.E i j) v) =
      Matrix.toEuclideanLin (E.E i j) (Matrix.toEuclideanLin P v)
    simp only [P, LinearEquiv.apply_symm_apply]
    exact hcomm i j v) g
  intro g x hx
  have hxfix : K.starProjection (e.symm x) = e.symm x :=
    Submodule.starProjection_eq_self_iff.mpr hx
  have hfix : K.starProjection (Matrix.toEuclideanLin (U g) (e.symm x)) =
      Matrix.toEuclideanLin (U g) (e.symm x) := by
    have h := congrArg (fun M => Matrix.toEuclideanLin M (e.symm x)) (hP g)
    dsimp only at h
    simp only [Matrix.toLpLin_apply, ← Matrix.mulVec_mulVec] at h
    change Matrix.toEuclideanLin P (Matrix.toEuclideanLin (U g) (e.symm x)) =
      Matrix.toEuclideanLin (U g) (Matrix.toEuclideanLin P (e.symm x)) at h
    simp only [P, LinearEquiv.apply_symm_apply] at h
    change K.starProjection (Matrix.toEuclideanLin (U g) (e.symm x)) =
      Matrix.toEuclideanLin (U g) (K.starProjection (e.symm x)) at h
    rw [hxfix] at h
    exact h
  exact Submodule.starProjection_eq_self_iff.mp hfix

/-- Every invariant subspace of the literal physical matrix-unit Lie action
is invariant under the actual tensor representation of U(d). -/
theorem physical_invariant_of_generators
    (S : Submodule ℂ ((Fin n → Fin d) → ℂ))
    (hS : ∀ i j x, x ∈ S → (TensorPowers.generators d n).E i j *ᵥ x ∈ S) :
    ∀ U x, x ∈ S → physicalRepresentation d n U *ᵥ x ∈ S :=
  invariant_of_commutant_bridge (physicalRepresentation d n) (TensorPowers.generators d n)
    (fun T hT => (tensorCommutant_iff_generators T).mpr hT) S hS

/-- Genuine invariant summands inherit the same Lie/group invariant-subspace
identity, with the actual compressed differential matrices. -/
theorem restricted_invariant_of_generators
    (R : Matrix.unitaryGroup (Fin d) ℂ →* Matrix A A ℂ)
    (J : Matrix (Fin n → Fin d) A ℂ) (hJ : Jᴴ * J = 1)
    (hJR : ∀ U, physicalRepresentation d n U * J = J * R U)
    (S : Submodule ℂ (A → ℂ))
    (hS : ∀ i j x, x ∈ S → (restrictedGenerators R J hJ hJR).E i j *ᵥ x ∈ S) :
    ∀ U x, x ∈ S → R U *ᵥ x ∈ S :=
  invariant_of_commutant_bridge R (restrictedGenerators R J hJ hJR)
    (restricted_commutant_of_generators R J hJ hJR) S hS

/-- Every nonzero vector in a genuine irreducible physical summand is cyclic
for its actual Lie generators; cyclicity is a conclusion, not an assumption. -/
theorem restricted_cyclicSpan_eq_top
    (R : Matrix.unitaryGroup (Fin d) ℂ →* Matrix A A ℂ)
    (J : Matrix (Fin n → Fin d) A ℂ) (hJ : Jᴴ * J = 1)
    (hJR : ∀ U, physicalRepresentation d n U * J = J * R U)
    (hirr : Representation.IsIrreducible (Twirling.matrixRepresentation R))
    (v : A → ℂ) (hv : v ≠ 0) :
    LiePBW.cyclicSpan (restrictedGenerators R J hJ hJR) v = ⊤ := by
  let F := restrictedGenerators R J hJ hJR
  let S := LiePBW.cyclicSpan F v
  have hS := restricted_invariant_of_generators R J hJ hJR S
    (fun i j _ hx => LiePBW.generator_preserves_cyclicSpan F v i j hx)
  let W : Subrepresentation (Twirling.matrixRepresentation R) :=
    Subrepresentation.mk S (fun g x hx => hS g x hx)
  rcases hirr.eq_bot_or_eq_top W with hzero | htop
  · have hm : v ∈ W.toSubmodule := LiePBW.self_mem_cyclicSpan F v
    rw [hzero] at hm
    exact (hv hm).elim
  · exact congrArg Subrepresentation.toSubmodule htop

end FreeEntropy.SchurWeyl
