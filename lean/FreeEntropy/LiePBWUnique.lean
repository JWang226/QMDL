/-
Copyright (c) 2026 Free Entropy formalization contributors.
See LICENSE and NOTICE in the repository root for license and attribution.
-/

import FreeEntropy.LiePBWHighest

/-! A highest vector generates a Lie-cyclic space with exactly one highest
line, derived from PBW spanning and the genuine adjoint relation. -/
noncomputable section
open Matrix
open scoped ComplexOrder
namespace FreeEntropy.LiePBW
open LieMatrixCasimir
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false

variable {d : ℕ} {H : Type*} [Fintype H] [DecidableEq H]

theorem highest_dot_lowering_word_zero (R : Generators d H) (u v : H → ℂ)
    (hraise : ∀ i j, i < j → R.E i j *ᵥ u = 0)
    (w : List (Root d)) (hw : w ≠ []) (hl : ∀ a ∈ w, a.2 < a.1) :
    star u ⬝ᵥ (word R w *ᵥ v) = 0 := by
  cases w with
  | nil => exact (hw rfl).elim
  | cons a w =>
    rw [word_cons, ← Matrix.mulVec_mulVec, dotProduct_mulVec]
    have hz : star u ᵥ* R.E a.1 a.2 = 0 := by
      rw [← R.adjoint a.2 a.1, Matrix.vecMul_conjTranspose, star_star,
        hraise a.2 a.1 (hl a List.mem_cons_self), star_zero]
    rw [hz, zero_dotProduct]

theorem highest_orthogonal_zero (R : Generators d H) (lam : Fin d → ℂ) (v u : H → ℂ)
    (hweight : ∀ i, R.E i i *ᵥ v = lam i • v)
    (hraise : ∀ i j, i < j → R.E i j *ᵥ v = 0)
    (hu : u ∈ cyclicSpan R v) (huraise : ∀ i j, i < j → R.E i j *ᵥ u = 0)
    (huv : star u ⬝ᵥ v = 0) : u = 0 := by
  have hall : ∀ x, x ∈ loweringSpan R v → star u ⬝ᵥ x = 0 := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨w, hl, rfl⟩ := hx
      by_cases hw : w = []
      · simpa only [hw, word_nil, Matrix.one_mulVec] using huv
      · exact highest_dot_lowering_word_zero R u v huraise w hw hl
    | zero => simp
    | add x y hx hy ihx ihy => simp [dotProduct_add, ihx, ihy]
    | smul c x hx ih => simp [dotProduct_smul, ih]
  apply dotProduct_star_self_eq_zero.mp
  apply hall u
  rwa [← cyclicSpan_eq_loweringSpan R lam v hweight hraise]

/-- Every vector in the generated Lie module killed by all raising operators
lies in the original highest line. No weight-multiplicity assertion is assumed. -/
theorem highest_line_unique (R : Generators d H) (lam : Fin d → ℂ) (v u : H → ℂ)
    (hv : v ≠ 0) (hweight : ∀ i, R.E i i *ᵥ v = lam i • v)
    (hraise : ∀ i j, i < j → R.E i j *ᵥ v = 0)
    (hu : u ∈ cyclicSpan R v) (huraise : ∀ i j, i < j → R.E i j *ᵥ u = 0) :
    ∃ c : ℂ, u = c • v := by
  let c : ℂ := (star v ⬝ᵥ u) / (star v ⬝ᵥ v)
  have hden : star v ⬝ᵥ v ≠ 0 := fun h => hv (dotProduct_star_self_eq_zero.mp h)
  have horth : star v ⬝ᵥ (u - c • v) = 0 := by
    rw [dotProduct_sub, dotProduct_smul]
    change (star v ⬝ᵥ u) - c * (star v ⬝ᵥ v) = 0
    dsimp [c]
    rw [div_mul_cancel₀ _ hden, sub_self]
  have horth' : star (u - c • v) ⬝ᵥ v = 0 := by
    rw [star_dotProduct, horth, star_zero]
  have hz : u - c • v = 0 := by
    apply highest_orthogonal_zero R lam v (u - c • v) hweight hraise
    · exact (cyclicSpan R v).sub_mem hu ((cyclicSpan R v).smul_mem c (self_mem_cyclicSpan R v))
    · intro i j hij
      simp only [Matrix.mulVec_sub, Matrix.mulVec_smul, huraise i j hij, hraise i j hij,
        smul_zero, sub_self]
    · exact horth'
  exact ⟨c, sub_eq_zero.mp hz⟩

end FreeEntropy.LiePBW
