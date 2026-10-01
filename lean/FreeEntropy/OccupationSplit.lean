/-
Copyright (c) 2026 Free Entropy formalization contributors.
See LICENSE and NOTICE in the repository root for license and attribution.
-/

import FreeEntropy.Occupation
import FreeEntropy.CartanChannel

/-!
# The concrete symmetric-power Cartan isometry

Splitting a word into two segments gives an isometry from occupations of
n+m letters to the tensor product of the two occupation spaces. The matrix
entries are derived from actual type-class sizes; no Cartan embedding is
assumed.
-/
noncomputable section
open scoped BigOperators Matrix Kronecker
open Matrix
namespace FreeEntropy.OccupationSplit
open Occupation WordTypes
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 700000
attribute [local instance] Classical.propDecidable

variable {d n m : ℕ}

def joinWords : ((Fin n → Fin d) × (Fin m → Fin d)) ≃ (Fin (n + m) → Fin d) :=
  (Equiv.sumArrowEquivProdArrow (Fin n) (Fin m) (Fin d)).symm.trans
    (finSumFinEquiv.arrowCongr (Equiv.refl (Fin d)))

@[simp] theorem joinWords_left (w : Fin n → Fin d) (v : Fin m → Fin d) (i : Fin n) :
    joinWords (w, v) (Fin.castAdd m i) = w i := by
  simp [joinWords, Equiv.arrowCongr]

@[simp] theorem joinWords_right (w : Fin n → Fin d) (v : Fin m → Fin d) (i : Fin m) :
    joinWords (w, v) (Fin.natAdd n i) = v i := by
  simp [joinWords, Equiv.arrowCongr]

theorem content_joinWords (w : Fin n → Fin d) (v : Fin m → Fin d) :
    content (joinWords (w, v)) = fun i => content w i + content v i := by
  funext i
  simp only [content, Finset.card_filter]
  rw [Fin.sum_univ_add]
  simp only [joinWords_left, joinWords_right]

/-- The large symmetric basis, with the tensor word coordinates regrouped. -/
def joinedBasis : Matrix ((Fin n → Fin d) × (Fin m → Fin d)) (Occupation d (n + m)) ℂ :=
  fun w a => basis (joinWords w) a

theorem joinedBasis_isometry : (joinedBasis (d := d) (n := n) (m := m))ᴴ *
    joinedBasis (d := d) (n := n) (m := m) = 1 := by
  ext a b
  have h := congrFun (congrFun (basis_isometry (d := d) (n := n + m)) a) b
  change (∑ w, star (basis (joinWords w) a) * basis (joinWords w) b) = _
  rw [Equiv.sum_comp joinWords (fun w => star (basis w a) * basis w b)]
  exact h

/-- Product of the two actual occupation-basis isometries. -/
def productBasis : Matrix ((Fin n → Fin d) × (Fin m → Fin d))
    (Occupation d n × Occupation d m) ℂ := basis ⊗ₖ basis

theorem productBasis_isometry : (productBasis (d := d) (n := n) (m := m))ᴴ *
    productBasis (d := d) (n := n) (m := m) = 1 := by
  unfold productBasis
  rw [Matrix.conjTranspose_kronecker, ← Matrix.mul_kronecker_mul,
    basis_isometry, basis_isometry, Matrix.one_kronecker_one]

/-- Concrete splitting coefficients, with the correct type-class normalization. -/
def split : Matrix (Occupation d n × Occupation d m) (Occupation d (n + m)) ℂ := fun ab c =>
  if (fun i => ab.1.val i + ab.2.val i) = c.val then
    (Real.sqrt (typeSize ab.1) : ℂ) * (Real.sqrt (typeSize ab.2) : ℂ) /
      (Real.sqrt (typeSize c) : ℂ) else 0

/-- Expanding the splitting coefficients exactly recovers the large basis. -/
theorem productBasis_mul_split : productBasis (d := d) (n := n) (m := m) * split =
    joinedBasis := by
  ext ⟨w, v⟩ c
  rw [Matrix.mul_apply, Finset.sum_eq_single (ofWord w, ofWord v)]
  · have hw : (Real.sqrt (typeSize (ofWord w)) : ℂ) ≠ 0 := by
      exact_mod_cast (Real.sqrt_pos.mpr (by exact_mod_cast typeSize_pos (ofWord w))).ne'
    have hv : (Real.sqrt (typeSize (ofWord v)) : ℂ) ≠ 0 := by
      exact_mod_cast (Real.sqrt_pos.mpr (by exact_mod_cast typeSize_pos (ofWord v))).ne'
    simp only [productBasis, Matrix.kronecker_apply, basis,
      show content w = (ofWord w).val from rfl, show content v = (ofWord v).val from rfl,
      ↓reduceIte, split, joinedBasis, content_joinWords]
    by_cases h : (fun i => content w i + content v i) = c.val
    · simp only [ofWord, h, ↓reduceIte]
      simp only [ofWord] at hw hv
      field_simp [hw, hv]
    · simp only [ofWord, h, ↓reduceIte, mul_zero]
  · rintro ⟨a, b⟩ _ hab
    have hne : content w ≠ a.val ∨ content v ≠ b.val := by
      by_contra! h
      exact hab (Prod.ext (Subtype.ext h.1.symm) (Subtype.ext h.2.symm))
    rcases hne with ha | hb
    · simp [productBasis, basis, ha]
    · simp [productBasis, basis, hb]
  · simp

/-- The actual symmetric Cartan embedding is isometric. -/
theorem split_isometry : (split (d := d) (n := n) (m := m))ᴴ *
    split (d := d) (n := n) (m := m) = 1 := by
  have h := joinedBasis_isometry (d := d) (n := n) (m := m)
  rw [← productBasis_mul_split, Matrix.conjTranspose_mul] at h
  calc
    _ = splitᴴ * (productBasisᴴ * productBasis) * split := by rw [productBasis_isometry]; simp
    _ = 1 := by simpa only [Matrix.mul_assoc] using h

theorem tensorVector_joinWords (z : Fin d → ℂ) (w : Fin n → Fin d) (v : Fin m → Fin d) :
    tensorVector z (joinWords (w, v)) = tensorVector z w * tensorVector z v := by
  unfold tensorVector
  rw [Fin.prod_univ_add]
  simp only [joinWords_left, joinWords_right]

/-- The splitting isometry sends the actual pure occupation vector to the
product of its two smaller occupation vectors. -/
theorem split_coefficients (z : Fin d → ℂ) :
    split *ᵥ coefficients (n := n + m) z =
      fun ab : Occupation d n × Occupation d m => coefficients z ab.1 * coefficients z ab.2 := by
  have he : productBasis *ᵥ (split *ᵥ coefficients (n := n + m) z) =
      productBasis *ᵥ (fun ab : Occupation d n × Occupation d m =>
        coefficients z ab.1 * coefficients z ab.2) := by
    rw [Matrix.mulVec_mulVec, productBasis_mul_split]
    funext w
    rcases w with ⟨w, v⟩
    have hleft : (joinedBasis *ᵥ coefficients (n := n + m) z) (w, v) =
        tensorVector z (joinWords (w, v)) :=
      congrFun (basis_mulVec_coefficients (n := n + m) z) (joinWords (w, v))
    rw [hleft, tensorVector_joinWords]
    simp only [Matrix.mulVec, dotProduct, productBasis, Matrix.kronecker_apply,
      Fintype.sum_prod_type]
    have hre (a : Occupation d n) (b : Occupation d m) :
        basis w a * basis v b * (coefficients z a * coefficients z b) =
          (basis w a * coefficients z a) * (basis v b * coefficients z b) := by ring
    simp only [hre, ← Finset.mul_sum, ← Finset.sum_mul]
    rw [show (∑ a : Occupation d n, basis w a * coefficients z a) = tensorVector z w from
      congrFun (basis_mulVec_coefficients (n := n) z) w]
    rw [show (∑ b : Occupation d m, basis v b * coefficients z b) = tensorVector z v from
      congrFun (basis_mulVec_coefficients (n := m) z) v]
  have hh := congrArg (fun f => (productBasis (d := d) (n := n) (m := m))ᴴ *ᵥ f) he
  simpa only [Matrix.mulVec_mulVec, ← Matrix.mul_assoc, productBasis_isometry,
    Matrix.one_mul, Matrix.one_mulVec] using hh

/-- Exact factorization of the rank-one density matrix under the Cartan embedding. -/
theorem split_pure (z : Fin d → ℂ) :
    split * TensorPowers.pure (coefficients (n := n + m) z) * splitᴴ =
      TensorPowers.pure (coefficients (n := n) z) ⊗ₖ
        TensorPowers.pure (coefficients (n := m) z) := by
  change split * Matrix.vecMulVec (coefficients z) (star (coefficients z)) * splitᴴ = _
  rw [Matrix.mul_vecMulVec, Matrix.vecMulVec_mul, ← Matrix.star_mulVec, split_coefficients]
  ext ⟨a, b⟩ ⟨c, e⟩
  simp only [Matrix.vecMulVec_apply, Pi.star_apply, star_mul', Matrix.kronecker_apply,
    TensorPowers.pure]
  ring

end FreeEntropy.OccupationSplit
