/-
Copyright (c) 2026 Free Entropy formalization contributors.
See LICENSE and NOTICE in the repository root for license and attribution.
-/

import FreeEntropy.WordTypes
import Mathlib.Data.Fin.Tuple.NatAntidiagonal
import FreeEntropy.TensorPowers

/-!
# The occupation basis of the symmetric tensor space

The columns are normalized uniform sums of words with a fixed content.
Their orthogonality is proved by disjointness of the actual word types.
-/
noncomputable section
open scoped BigOperators Matrix
namespace FreeEntropy.Occupation
open Matrix WordTypes
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
set_option linter.dupNamespace false
attribute [local instance] Classical.propDecidable

/-- Finite occupations of n letters in d modes. -/
def Occupation (d n : ℕ) := {lam : Fin d → ℕ // ∑ i, lam i = n}

instance (d n : ℕ) : Fintype (Occupation d n) :=
  Fintype.ofFinset (Finset.Nat.antidiagonalTuple d n) (fun _ => Finset.Nat.mem_antidiagonalTuple)

instance (d n : ℕ) : DecidableEq (Occupation d n) := Classical.decEq _

variable {d n : ℕ}

theorem content_sum (w : Fin n → Fin d) : ∑ i, content w i = n := by
  have h := Finset.card_eq_sum_card_fiberwise
    (s := Finset.univ) (t := Finset.univ) (f := w) (fun _ _ => Finset.mem_univ _)
  simpa only [Finset.card_univ, Fintype.card_fin, content] using h.symm

def ofWord (w : Fin n → Fin d) : Occupation d n := ⟨content w, content_sum w⟩

/-- Each occupation has a word, constructed from a bijection with its cells. -/
theorem words_nonempty (a : Occupation d n) : Nonempty (Words (n := n) a.val) := by
  have hc : Fintype.card ((i : Fin d) × Fin (a.val i)) = Fintype.card (Fin n) := by
    simpa only [Fintype.card_sigma, Fintype.card_fin] using a.property
  let e := Fintype.equivOfCardEq hc
  let w : Fin n → Fin d := fun t => (e.symm t).fst
  have hw : content w = a.val := by
    funext i
    have hf : Finset.univ.filter (fun t => w t = i) =
        Finset.univ.image (fun j : Fin (a.val i) => e ⟨i, j⟩) := by
      ext t
      constructor
      · intro ht
        have ht' : (e.symm t).fst = i := (Finset.mem_filter.mp ht).2
        rcases he : e.symm t with ⟨k, j⟩
        have hk : k = i := by simpa only [he] using ht'
        subst k
        refine Finset.mem_image.mpr ⟨j, Finset.mem_univ _, ?_⟩
        have he' := e.apply_symm_apply t
        rwa [he] at he'
      · rintro ht
        obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp ht
        simp [w]
    have hi : Function.Injective (fun j : Fin (a.val i) => e ⟨i, j⟩) := by
      intro j k h
      exact Sigma.mk.inj_iff.mp (e.injective h) |>.2 |> eq_of_heq
    rw [content, hf, Finset.card_image_of_injective _ hi, Finset.card_univ, Fintype.card_fin]
  exact ⟨⟨w, hw⟩⟩

def typeSize (a : Occupation d n) : ℕ := Fintype.card (Words (n := n) a.val)

theorem typeSize_pos (a : Occupation d n) : 0 < typeSize a := by
  letI := words_nonempty a
  exact Fintype.card_pos

/-- Occupation-basis isometry into the full tensor word basis. -/
def basis : Matrix (Fin n → Fin d) (Occupation d n) ℂ := fun w a =>
  if content w = a.val then ((Real.sqrt (typeSize a) : ℝ) : ℂ)⁻¹ else 0

def tensorVector (z : Fin d → ℂ) (w : Fin n → Fin d) : ℂ := ∏ t, z (w t)

def coefficients (z : Fin d → ℂ) (a : Occupation d n) : ℂ :=
  (Real.sqrt (typeSize a) : ℂ) * ∏ i, z i ^ a.val i

theorem basis_isometry : (basis (d := d) (n := n))ᴴ * basis (d := d) (n := n) = 1 := by
  ext a b
  classical
  rw [Matrix.mul_apply]
  by_cases hab : a = b
  · subst b
    have hpos : 0 < (typeSize a : ℝ) := by exact_mod_cast typeSize_pos a
    have hs : (Real.sqrt (typeSize a) : ℂ) ≠ 0 := by
      exact_mod_cast (Real.sqrt_pos.mpr hpos).ne'
    have hsq : (Real.sqrt (typeSize a) : ℂ) ^ 2 = (typeSize a : ℂ) := by
      exact_mod_cast Real.sq_sqrt hpos.le
    have he : (∑ w : Fin n → Fin d, star (basis w a) * basis w a) =
        (typeSize a : ℂ) * ((Real.sqrt (typeSize a) : ℂ)⁻¹ *
          (Real.sqrt (typeSize a) : ℂ)⁻¹) := by
      have hb (w : Fin n → Fin d) : star (basis w a) * basis w a =
          if content w = a.val then ((Real.sqrt (typeSize a) : ℂ)⁻¹ *
            (Real.sqrt (typeSize a) : ℂ)⁻¹) else 0 := by
        by_cases hw : content w = a.val <;> simp [basis, hw]
      simp only [hb, ← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
      congr 1
      simp only [typeSize, Words, Fintype.card_subtype]
    simpa only [Matrix.conjTranspose_apply, Matrix.one_apply_eq] using
      he.trans (by rw [← sq, inv_pow, hsq]; exact mul_inv_cancel₀ (by exact_mod_cast hpos.ne'))
  · have hab' : a.val ≠ b.val := fun h => hab (Subtype.ext h)
    have hz (w : Fin n → Fin d) : star (basis w a) * basis w b = 0 := by
      by_cases ha : content w = a.val
      · have hb : content w ≠ b.val := fun hb => hab' (ha.symm.trans hb)
        simp [basis, hb]
      · simp [basis, ha]
    simp only [Matrix.conjTranspose_apply, hz, Finset.sum_const_zero,
      Matrix.one_apply_ne hab] 

/-- Every pure tensor has exact occupation coordinates. -/
theorem basis_mulVec_coefficients (z : Fin d → ℂ) :
    basis *ᵥ coefficients (n := n) z = tensorVector (n := n) z := by
  classical
  funext w
  rw [Matrix.mulVec, dotProduct]
  rw [Finset.sum_eq_single (ofWord w)]
  · have hs : (Real.sqrt (typeSize (ofWord w)) : ℂ) ≠ 0 := by
      exact_mod_cast (Real.sqrt_pos.mpr (by exact_mod_cast typeSize_pos (ofWord w))).ne'
    rw [basis, if_pos (show content w = (ofWord w).val from rfl), coefficients,
      inv_mul_cancel_left₀ hs]
    simpa only [tensorVector, content, Finset.prod_const] using
      (Finset.prod_fiberwise' Finset.univ w z)
  · intro a _ ha
    have hne : content w ≠ a.val := fun h => ha (Subtype.ext h.symm)
    simp [basis, hne]
  · simp

/-- The physical tensor-power pure matrix is exactly supported in this basis. -/
theorem tensor_pure_embedding (z : Fin d → ℂ) :
    TensorPowers.matrix n (TensorPowers.pure z) =
      basis * TensorPowers.pure (coefficients (n := n) z) * basisᴴ := by
  rw [TensorPowers.matrix_pure]
  have he := basis_mulVec_coefficients (n := n) z
  change basis *ᵥ coefficients z = TensorPowers.vector n z at he
  change Matrix.vecMulVec (TensorPowers.vector n z) (star (TensorPowers.vector n z)) =
    basis * Matrix.vecMulVec (coefficients z) (star (coefficients z)) * basisᴴ
  rw [Matrix.mul_vecMulVec, Matrix.vecMulVec_mul, ← Matrix.star_mulVec, he]

end FreeEntropy.Occupation
