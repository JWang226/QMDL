/-
Copyright (c) 2026 Free Entropy formalization contributors.
See LICENSE and NOTICE in the repository root for license and attribution.
-/

import FreeEntropy.SchurWeylMultiplicity
import Mathlib.LinearAlgebra.Matrix.Rank

/-!
# Multiplicity bounds from actual highest-weight vectors

A physical torus eigenvector is supported on its literal word-content class.
Restricting orthonormal vectors of one weight to that finite class preserves
their Gram matrix. Matrix rank then bounds their number by the actual word
count. Applied to equivalent irreducible copies, this proves the multiplicity
bound needed for concentration without a tableau or Specht-dimension formula.
-/
noncomputable section
open scoped BigOperators ComplexOrder MatrixOrder
open Matrix
namespace FreeEntropy.SchurWeyl
open Occupation WordTypes
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
set_option linter.unusedSectionVars false
attribute [local instance] Classical.propDecidable
variable {d n : ℕ}
variable {A M : Type*} [Fintype A] [DecidableEq A] [Fintype M] [DecidableEq M]

/-- The actual diagonal-unitary eigenvector equation forces exact word support. -/
theorem torus_eigenvector_supported (a : Occupation d n) (v : (Fin n → Fin d) → ℂ)
    (hv : ∀ z : Fin d → ℂ, ∀ hz : ∀ i, ‖z i‖ = 1,
      TensorPowers.matrix n (diagonalUnitary z hz).val *ᵥ v = character z a • v)
    (w : Fin n → Fin d) (hw : content w ≠ a.val) : v w = 0 := by
  have hwa : ofWord w ≠ a := fun h => hw (congrArg Subtype.val h)
  obtain ⟨z, hz, hchar⟩ := character_separates (ofWord w) a hwa
  have h := congrFun (hv z hz) w
  change (TensorPowers.matrix n (Matrix.diagonal z) *ᵥ v) w = _ at h
  rw [tensor_diagonal] at h
  have he : (TensorPowers.vector n z w) * v w = character z a * v w := by
    simpa [Matrix.mulVec, dotProduct, Matrix.diagonal_apply, Pi.smul_apply, smul_eq_mul] using h
  rw [tensorVector_eq_character] at he
  have hz' : (character z (ofWord w) - character z a) * v w = 0 := by
    rw [sub_mul, he, sub_self]
  exact (mul_eq_zero.mp hz').resolve_left (sub_ne_zero.mpr hchar)

/-- An isometry whose columns lie in one literal word type has at most as
many columns as words of that type. -/
theorem orthonormal_supported_card_le (a : Occupation d n)
    (V : Matrix (Fin n → Fin d) M ℂ) (hV : Vᴴ * V = 1)
    (hsupport : ∀ w, content w ≠ a.val → ∀ i, V w i = 0) :
    Fintype.card M ≤ Fintype.card (Words (n := n) a.val) := by
  let W : Matrix (Words (n := n) a.val) M ℂ := fun w i => V w.val i
  have hW : Wᴴ * W = 1 := by
    ext i j
    have hs : (∑ w : Words (n := n) a.val, star (V w.val i) * V w.val j) =
        ∑ w : Fin n → Fin d, star (V w i) * V w j := by
      have hsub : (∑ w : Words (n := n) a.val, star (V w.val i) * V w.val j) =
          ∑ w ∈ Finset.univ.filter (fun w : Fin n → Fin d => content w = a.val),
            star (V w i) * V w j := by
        apply Finset.sum_bij (fun w _ => w.val)
        · intro w _
          exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, w.property⟩
        · intro w _ v _ he
          exact Subtype.ext he
        · intro w hw
          exact ⟨⟨w, (Finset.mem_filter.mp hw).2⟩, Finset.mem_univ _, rfl⟩
        · intro w _
          rfl
      rw [hsub]
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro w _
      by_cases hw : content w = a.val
      · simp [hw]
      · simp [hw, hsupport w hw i]
    change (∑ w : Words (n := n) a.val, star (V w.val i) * V w.val j) = _
    rw [hs]
    exact congrFun (congrFun hV i) j
  have hr := (Matrix.rank_mul_le_right Wᴴ W).trans (Matrix.rank_le_card_height W)
  rwa [hW, Matrix.rank_one] at hr

/-- The multiplicity of an actual physical torus weight is bounded by the
finite number of words having that content. -/
theorem orthonormal_weight_card_le (a : Occupation d n)
    (V : Matrix (Fin n → Fin d) M ℂ) (hV : Vᴴ * V = 1)
    (hweight : ∀ i, ∀ z : Fin d → ℂ, ∀ hz : ∀ j, ‖z j‖ = 1,
      TensorPowers.matrix n (diagonalUnitary z hz).val *ᵥ (fun w => V w i) =
        character z a • (fun w => V w i)) :
    Fintype.card M ≤ Fintype.card (Words (n := n) a.val) := by
  apply orthonormal_supported_card_le a V hV
  intro w hw i
  exact torus_eigenvector_supported a (fun w => V w i) (hweight i) w hw

/-- The image of a common unit vector in orthogonal isometric copies. -/
def copyVectors (J : M → Matrix (Fin n → Fin d) A ℂ) (v : A → ℂ) :
    Matrix (Fin n → Fin d) M ℂ := fun w i => (J i *ᵥ v) w

theorem copyVectors_isometry (J : M → Matrix (Fin n → Fin d) A ℂ)
    (hJ : ∀ i, (J i)ᴴ * J i = 1)
    (horth : ∀ i j, i ≠ j → (J i)ᴴ * J j = 0)
    (v : A → ℂ) (hv : star v ⬝ᵥ v = 1) : (copyVectors J v)ᴴ * copyVectors J v = 1 := by
  ext i j
  change star (J i *ᵥ v) ⬝ᵥ (J j *ᵥ v) = _
  rw [Matrix.star_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul]
  by_cases hij : i = j
  · subst j
    rw [hJ i, Matrix.vecMul_one, hv, Matrix.one_apply_eq]
  · rw [horth i j hij, Matrix.vecMul_zero, zero_dotProduct, Matrix.one_apply_ne hij]

/-- Multiplicity is derived from a normalized highest-weight vector and
actual equivalent representation copies, without a multiplicity estimate. -/
theorem copy_multiplicity_le_words
    (R : Matrix.unitaryGroup (Fin d) ℂ →* Matrix A A ℂ)
    (J : M → Matrix (Fin n → Fin d) A ℂ)
    (hJ : ∀ i, (J i)ᴴ * J i = 1)
    (horth : ∀ i j, i ≠ j → (J i)ᴴ * J j = 0)
    (hJR : ∀ i U, physicalRepresentation d n U * J i = J i * R U)
    (a : Occupation d n) (v : A → ℂ) (hv : star v ⬝ᵥ v = 1)
    (hweight : ∀ z : Fin d → ℂ, ∀ hz : ∀ j, ‖z j‖ = 1,
      R (diagonalUnitary z hz) *ᵥ v = character z a • v) :
    Fintype.card M ≤ Fintype.card (Words (n := n) a.val) := by
  apply orthonormal_weight_card_le a (copyVectors J v) (copyVectors_isometry J hJ horth v hv)
  intro i z hz
  change physicalRepresentation d n (diagonalUnitary z hz) *ᵥ (J i *ᵥ v) =
    character z a • (J i *ᵥ v)
  rw [Matrix.mulVec_mulVec, hJR, ← Matrix.mulVec_mulVec, hweight, Matrix.mulVec_smul]

/-- The genuine representation-copy count satisfies the entropy bound needed
by the pointwise Schur estimate; no tableau multiplicity identity is needed. -/
theorem copy_multiplicity_entropy_bound
    (R : Matrix.unitaryGroup (Fin d) ℂ →* Matrix A A ℂ)
    (J : M → Matrix (Fin n → Fin d) A ℂ)
    (hJ : ∀ i, (J i)ᴴ * J i = 1)
    (horth : ∀ i j, i ≠ j → (J i)ᴴ * J j = 0)
    (hJR : ∀ i U, physicalRepresentation d n U * J i = J i * R U)
    (a : Occupation d n) (v : A → ℂ) (hv : star v ⬝ᵥ v = 1)
    (hweight : ∀ z : Fin d → ℂ, ∀ hz : ∀ j, ‖z j‖ = 1,
      R (diagonalUnitary z hz) *ᵥ v = character z a • v)
    (hn : 0 < n) (x : Fin d → ℝ) (hx : ∀ i, 0 < x i) :
    (Fintype.card M : ℝ) * monomial a.val x ≤
      Real.exp (-(n : ℝ) * FiniteConcentration.kl (empirical a.val n) x) := by
  have hcount : (Fintype.card M : ℝ) ≤ Fintype.card (Words (n := n) a.val) := by
    exact_mod_cast copy_multiplicity_le_words R J hJ horth hJR a v hv hweight
  exact (mul_le_mul_of_nonneg_right hcount
    (Finset.prod_nonneg (fun i _ => pow_nonneg (hx i).le _))).trans
      (type_probability_le_exp_neg_kl a.val hn a.property x hx)

end FreeEntropy.SchurWeyl
