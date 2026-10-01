/-
Copyright (c) 2026 Free Entropy formalization contributors.
See LICENSE and NOTICE in the repository root for license and attribution.
-/

import FreeEntropy.LieHighestEquivalence

/-! Same-highest-weight equivalences are genuinely unitary after a scalar
normalization derived from the positive Gram matrix. -/
noncomputable section
open Matrix
open scoped ComplexOrder
namespace FreeEntropy.LiePBW
open LieMatrixCasimir
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000
variable {d : ℕ} {H K : Type*} [Fintype H] [DecidableEq H] [Fintype K] [DecidableEq K]

theorem commutant_scalar_of_highest (R : Generators d H) (lam : Fin d → ℂ)
    (v : H → ℂ) (hv : v ≠ 0) (hweight : ∀ i, R.E i i *ᵥ v = lam i • v)
    (hraise : ∀ i j, i < j → R.E i j *ᵥ v = 0) (hcyc : cyclicSpan R v = ⊤)
    (T : Matrix H H ℂ) (hT : ∀ i j, T * R.E i j = R.E i j * T) :
    ∃ c : ℂ, T = c • 1 := by
  have hmem : T *ᵥ v ∈ cyclicSpan R v := hcyc.symm ▸ Submodule.mem_top
  have hTr (i j : Fin d) (hij : i < j) : R.E i j *ᵥ (T *ᵥ v) = 0 := by
    rw [Matrix.mulVec_mulVec, ← hT, ← Matrix.mulVec_mulVec, hraise i j hij, Matrix.mulVec_zero]
  obtain ⟨c, hc⟩ := highest_line_unique R lam v (T *ᵥ v) hv hweight hraise hmem hTr
  refine ⟨c, ?_⟩
  apply Matrix.toLin'.injective
  apply LinearMap.ext
  intro x
  have hx := commuting_operator_scalar_on_cyclicSpan R v T hT c hc
    (show x ∈ cyclicSpan R v from hcyc.symm ▸ Submodule.mem_top)
  simpa only [Matrix.toLin'_apply, Matrix.smul_mulVec, Matrix.one_mulVec] using hx

theorem gram_commutes (R : Generators d H) (S : Generators d K) (F : Matrix K H ℂ)
    (hF : ∀ i j, F * R.E i j = S.E i j * F) (i j : Fin d) :
    (Fᴴ * F) * R.E i j = R.E i j * (Fᴴ * F) := by
  have ha := congrArg Matrix.conjTranspose (hF j i)
  simp only [Matrix.conjTranspose_mul, R.adjoint, S.adjoint] at ha
  calc
    _ = Fᴴ * (F * R.E i j) := Matrix.mul_assoc _ _ _
    _ = Fᴴ * (S.E i j * F) := by rw [hF]
    _ = (Fᴴ * S.E i j) * F := (Matrix.mul_assoc _ _ _).symm
    _ = _ := by rw [← ha, Matrix.mul_assoc]

/-- A bijective intertwiner between highest cyclic star-representations can
be normalized to a rectangular unitary, intertwining the actual generators. -/
theorem exists_highest_unitary (R : Generators d H) (S : Generators d K)
    (lam : Fin d → ℂ) (v : H → ℂ) (w : K → ℂ) (hv : v ≠ 0) (hw : w ≠ 0)
    (hvweight : ∀ i, R.E i i *ᵥ v = lam i • v)
    (hwweight : ∀ i, S.E i i *ᵥ w = lam i • w)
    (hvraise : ∀ i j, i < j → R.E i j *ᵥ v = 0)
    (hwraise : ∀ i j, i < j → S.E i j *ᵥ w = 0)
    (hvcyc : cyclicSpan R v = ⊤) (hwcyc : cyclicSpan S w = ⊤) :
    ∃ W : Matrix K H ℂ, Wᴴ * W = 1 ∧ W * Wᴴ = 1 ∧
      ∀ i j, W * R.E i j = S.E i j * W := by
  obtain ⟨F, hbij, hFv, hF⟩ := exists_highest_matrixEquiv R S lam v w hv hw
    hvweight hwweight hvraise hwraise hvcyc hwcyc
  obtain ⟨c, hc⟩ := commutant_scalar_of_highest R lam v hv hvweight hvraise hvcyc
    (Fᴴ * F) (gram_commutes R S F hF)
  obtain ⟨a, ha⟩ : ∃ a, v a ≠ 0 := by
    by_contra hn
    push_neg at hn
    exact hv (funext hn)
  have hcpos : 0 ≤ c := by
    have h := (Matrix.posSemidef_conjTranspose_mul_self F).diag_nonneg (i := a)
    simpa [hc] using h
  have hc0 : c ≠ 0 := by
    intro he
    have hF0 : F = 0 := Matrix.conjTranspose_mul_self_eq_zero.mp (by simp [hc, he])
    exact hw (by simpa only [hF0, Matrix.zero_mulVec] using hFv.symm)
  have hcre : 0 < c.re := by
    obtain ⟨hn, hi⟩ := Complex.nonneg_iff.mp hcpos
    have hne : c.re ≠ 0 := by
      intro he
      apply hc0
      exact Complex.ext he hi.symm
    exact lt_of_le_of_ne hn hne.symm
  have hcReal : (c.re : ℂ) = c := by
    apply Complex.ext
    · rfl
    · exact (Complex.nonneg_iff.mp hcpos).2
  have hgram : Fᴴ * F = c.re • (1 : Matrix H H ℂ) := by
    rw [hc]
    ext i j
    simp only [Matrix.smul_apply, Complex.real_smul, hcReal, smul_eq_mul]
  have hs : Real.sqrt c.re ≠ 0 := (Real.sqrt_pos.mpr hcre).ne'
  have hnorm : (Real.sqrt c.re)⁻¹ * ((Real.sqrt c.re)⁻¹ * c.re) = 1 := by
    have he := Real.sq_sqrt hcre.le
    field_simp
    nlinarith
  let W : Matrix K H ℂ := (Real.sqrt c.re)⁻¹ • F
  have hW : Wᴴ * W = 1 := by
    simp only [W, Matrix.conjTranspose_smul, star_trivial, Matrix.smul_mul,
      Matrix.mul_smul, hgram, smul_smul, hnorm, one_smul]
  have hsurj : Function.Surjective (fun x => W *ᵥ x) := by
    intro y
    obtain ⟨x, rfl⟩ := hbij.2 y
    refine ⟨Real.sqrt c.re • x, ?_⟩
    simp only [W, Matrix.smul_mulVec, Matrix.mulVec_smul, smul_smul, mul_inv_cancel₀ hs, one_smul]
  refine ⟨W, hW, ?_, ?_⟩
  · apply Matrix.toLin'.injective
    apply LinearMap.ext
    intro y
    obtain ⟨x, rfl⟩ := hsurj y
    change (W * Wᴴ) *ᵥ (W *ᵥ x) = (1 : Matrix K K ℂ) *ᵥ (W *ᵥ x)
    rw [Matrix.mulVec_mulVec, Matrix.mul_assoc, hW, Matrix.mul_one, Matrix.one_mulVec]
  · intro i j
    simp only [W, Matrix.smul_mul, Matrix.mul_smul, hF]

end FreeEntropy.LiePBW
