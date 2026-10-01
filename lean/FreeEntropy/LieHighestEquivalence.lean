/-
Copyright (c) 2026 Free Entropy formalization contributors.
See LICENSE and NOTICE in the repository root for license and attribution.
-/

import FreeEntropy.LieDirectSum

/-! Uniqueness of an actual highest-weight representation: a cyclic highest
vector in the block direct sum constructs the equivalence, with no
classification theorem taken as an assumption. -/
noncomputable section
open Matrix
namespace FreeEntropy.LiePBW
open LieMatrixCasimir
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000
variable {d : ℕ} {H K : Type*} [Fintype H] [DecidableEq H] [Fintype K] [DecidableEq K]

theorem exists_highest_linearEquiv (R : Generators d H) (S : Generators d K)
    (lam : Fin d → ℂ) (v : H → ℂ) (w : K → ℂ) (hv : v ≠ 0) (hw : w ≠ 0)
    (hvweight : ∀ i, R.E i i *ᵥ v = lam i • v)
    (hwweight : ∀ i, S.E i i *ᵥ w = lam i • w)
    (hvraise : ∀ i j, i < j → R.E i j *ᵥ v = 0)
    (hwraise : ∀ i j, i < j → S.E i j *ᵥ w = 0)
    (hvcyc : cyclicSpan R v = ⊤) (hwcyc : cyclicSpan S w = ⊤) :
    ∃ e : (H → ℂ) ≃ₗ[ℂ] (K → ℂ), e v = w ∧
      ∀ i j x, e (R.E i j *ᵥ x) = S.E i j *ᵥ e x := by
  let T := directSum R S
  let z : H ⊕ K → ℂ := Sum.elim v w
  let C := cyclicSpan T z
  let eH : C ≃ₗ[ℂ] (H → ℂ) := cyclicIntertwinerEquiv T R lam z
    (directSum_weight R S lam v w hvweight hwweight) (directSum_raise R S v w hvraise hwraise)
    firstCoordinate (firstCoordinate_intertwines R S) hv hvcyc
  let eK : C ≃ₗ[ℂ] (K → ℂ) := cyclicIntertwinerEquiv T S lam z
    (directSum_weight R S lam v w hvweight hwweight) (directSum_raise R S v w hvraise hwraise)
    secondCoordinate (secondCoordinate_intertwines R S) hw hwcyc
  let e := eH.symm.trans eK
  have heH (a : C) : eH a = firstCoordinate (a : H ⊕ K → ℂ) := rfl
  have heK (a : C) : eK a = secondCoordinate (a : H ⊕ K → ℂ) := rfl
  refine ⟨e, ?_, ?_⟩
  · let a : C := ⟨z, self_mem_cyclicSpan T z⟩
    have hv' : eH a = v := rfl
    have hw' : eK a = w := rfl
    rw [← hv']
    simpa only [e, LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply] using hw'
  · intro i j x
    let a : C := eH.symm x
    let b : C := ⟨T.E i j *ᵥ a, generator_preserves_cyclicSpan T z i j a.property⟩
    have hbH : eH b = R.E i j *ᵥ x := by
      rw [heH]
      change firstCoordinate ((directSum R S).E i j *ᵥ a) = _
      rw [firstCoordinate_intertwines]
      change R.E i j *ᵥ (eH (eH.symm x)) = _
      rw [eH.apply_symm_apply]
    have hbK : eK b = S.E i j *ᵥ e x := by
      rw [heK]
      change secondCoordinate ((directSum R S).E i j *ᵥ a) = _
      rw [secondCoordinate_intertwines]
      rfl
    rw [← hbH]
    simpa only [e, LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply] using hbK

/-- In coordinate matrices the constructed equivalence is a bijective
intertwiner of every actual matrix Lie generator. -/
theorem exists_highest_matrixEquiv (R : Generators d H) (S : Generators d K)
    (lam : Fin d → ℂ) (v : H → ℂ) (w : K → ℂ) (hv : v ≠ 0) (hw : w ≠ 0)
    (hvweight : ∀ i, R.E i i *ᵥ v = lam i • v)
    (hwweight : ∀ i, S.E i i *ᵥ w = lam i • w)
    (hvraise : ∀ i j, i < j → R.E i j *ᵥ v = 0)
    (hwraise : ∀ i j, i < j → S.E i j *ᵥ w = 0)
    (hvcyc : cyclicSpan R v = ⊤) (hwcyc : cyclicSpan S w = ⊤) :
    ∃ F : Matrix K H ℂ, Function.Bijective (fun x => F *ᵥ x) ∧ F *ᵥ v = w ∧
      ∀ i j, F * R.E i j = S.E i j * F := by
  obtain ⟨e, he, hinter⟩ := exists_highest_linearEquiv R S lam v w hv hw hvweight hwweight
    hvraise hwraise hvcyc hwcyc
  let F : Matrix K H ℂ := LinearMap.toMatrix' e.toLinearMap
  have hF (x : H → ℂ) : F *ᵥ x = e x :=
    congrArg (fun f : (H → ℂ) →ₗ[ℂ] (K → ℂ) => f x) (Matrix.toLin'_toMatrix' e.toLinearMap)
  refine ⟨F, ?_, (hF v).trans he, ?_⟩
  · simpa only [hF] using e.bijective
  · intro i j
    apply Matrix.toLin'.injective
    apply LinearMap.ext
    intro x
    change (F * R.E i j) *ᵥ x = (S.E i j * F) *ᵥ x
    simpa only [← Matrix.mulVec_mulVec, hF] using hinter i j x

end FreeEntropy.LiePBW
