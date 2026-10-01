/-
Copyright (c) 2026 Free Entropy formalization contributors.
See LICENSE and NOTICE in the repository root for license and attribution.
-/

import FreeEntropy.OccupationTorus

/-! The actual symmetric-power commutant is scalar once a physical unitary
with a nonzero column is exhibited. That unitary is constructed separately. -/
noncomputable section
open scoped BigOperators
open Matrix
namespace FreeEntropy.Occupation
open WordTypes
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
variable {d n : ℕ}

def highestOccupation (i₀ : Fin d) : Occupation d n := ofWord (fun _ => i₀)

theorem highestOccupation_val (i₀ i : Fin d) :
    (highestOccupation (n := n) i₀).val i = if i = i₀ then n else 0 := by
  by_cases h : i = i₀
  · subst i; simp [highestOccupation, ofWord, content]
  · simp [highestOccupation, ofWord, content, h, Ne.symm h]

theorem coefficients_single_support (i₀ : Fin d) (a : Occupation d n)
    (ha : a ≠ highestOccupation i₀) : coefficients (Pi.single i₀ 1) a = 0 := by
  have he : ∃ j, j ≠ i₀ ∧ a.val j ≠ 0 := by
    by_contra hn
    push_neg at hn
    have hi : a.val i₀ = n := by
      have hsum : ∑ j, a.val j = a.val i₀ := by
        apply Finset.sum_eq_single i₀
        · intro j _ hji; exact hn j hji
        · simp
      exact hsum.symm.trans a.property
    apply ha
    apply Subtype.ext
    funext j
    rw [highestOccupation_val]
    by_cases hji : j = i₀
    · simpa [hji] using hi
    · simp [hji, hn j hji]
  obtain ⟨j, hji, hj⟩ := he
  have hp : (∏ i, ((Pi.single i₀ (1 : ℂ) : Fin d → ℂ) i) ^ a.val i) = 0 := by
    apply Finset.prod_eq_zero (Finset.mem_univ j)
    simp [Pi.single_eq_of_ne hji, hj]
  unfold coefficients
  rw [hp, mul_zero]

theorem coefficients_nonzero (z : Fin d → ℂ) (hz : ∀ i, z i ≠ 0) (a : Occupation d n) :
    coefficients z a ≠ 0 := by
  apply mul_ne_zero
  · exact_mod_cast (Real.sqrt_pos.mpr (by exact_mod_cast typeSize_pos a)).ne'
  · exact Finset.prod_ne_zero_iff.mpr (fun i _ => pow_ne_zero _ (hz i))

/-- Scalarity follows from torus weight separation and one concrete mixing
unitary; no irreducibility hypothesis enters this argument. -/
theorem commutant_scalar_of_nonzero_column (i₀ : Fin d)
    (U : Matrix.unitaryGroup (Fin d) ℂ) (hcol : ∀ i, U.val i i₀ ≠ 0)
    (T : Matrix (Occupation d n) (Occupation d n) ℂ)
    (hT : ∀ W : Matrix.unitaryGroup (Fin d) ℂ,
      T * symmetricMatrix (n := n) W.val = symmetricMatrix (n := n) W.val * T) :
    ∃ c : ℂ, T = c • (1 : Matrix (Occupation d n) (Occupation d n) ℂ) := by
  let a₀ := highestOccupation (n := n) i₀
  let c := T a₀ a₀
  have hd := commutant_diagonal T hT
  have heigen : T *ᵥ coefficients (n := n) (Pi.single i₀ 1) =
      c • coefficients (n := n) (Pi.single i₀ 1) := by
    rw [hd]
    funext a
    simp only [Matrix.mulVec_diagonal, Pi.smul_apply, smul_eq_mul]
    by_cases ha : a = a₀
    · subst a; rfl
    · rw [coefficients_single_support i₀ a ha]
      simp
  have hcomm := congrArg (fun A : Matrix (Occupation d n) (Occupation d n) ℂ =>
    A *ᵥ coefficients (n := n) (Pi.single i₀ 1)) (hT U)
  dsimp only at hcomm
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, heigen, Matrix.mulVec_smul,
    coefficients_action] at hcomm
  have hcolv : U.val *ᵥ Pi.single i₀ 1 = fun i => U.val i i₀ := by
    funext i
    simp [Matrix.mulVec, dotProduct, Pi.single_apply]
  rw [hcolv, hd] at hcomm
  have hdiag (a : Occupation d n) : T a a = c := by
    have h := congrFun hcomm a
    simp only [Matrix.mulVec_diagonal, Pi.smul_apply, smul_eq_mul] at h
    exact mul_right_cancel₀ (coefficients_nonzero _ hcol a) h
  refine ⟨c, ?_⟩
  rw [hd]
  ext a b
  by_cases hab : a = b
  · subst b; simp [hdiag]
  · simp [Matrix.diagonal_apply_ne _ hab, Matrix.one_apply_ne hab]

end FreeEntropy.Occupation
