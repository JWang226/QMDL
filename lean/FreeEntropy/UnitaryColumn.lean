/-
Copyright (c) 2026 Free Entropy formalization contributors.
See LICENSE and NOTICE in the repository root for license and attribution.
-/

import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! Concrete unitary matrices with a prescribed normalized column. -/

noncomputable section
open Matrix
open scoped BigOperators ComplexInnerProductSpace

namespace FreeEntropy.UnitaryColumn

variable {H : Type*} [Fintype H] [DecidableEq H]

/-- Extend a single unit vector to a genuine orthonormal basis and take
its change-of-basis matrix. -/
theorem exists_unitary_column (i₀ : H) (z : EuclideanSpace ℂ H) (hz : ‖z‖ = 1) :
    ∃ U : Matrix.unitaryGroup H ℂ, ∀ i, (U : Matrix H H ℂ) i i₀ = z i := by
  classical
  have ho : Orthonormal ℂ (({i₀} : Set H).restrict (fun _ : H => z)) := by
    apply orthonormal_iff_ite.mpr
    intro i j
    have hij : i = j := Subtype.ext (by
      have hi := Set.mem_singleton_iff.mp i.property
      have hj := Set.mem_singleton_iff.mp j.property
      exact hi.trans hj.symm)
    simp [Set.restrict_apply, hij, inner_self_eq_norm_sq_to_K, hz]
  obtain ⟨b, hb⟩ := ho.exists_orthonormalBasis_extension_of_card_eq
    (finrank_euclideanSpace (𝕜 := ℂ) (ι := H))
  let a := EuclideanSpace.basisFun H ℂ
  refine ⟨⟨a.toBasis.toMatrix b, a.toMatrix_orthonormalBasis_mem_unitary b⟩, ?_⟩
  intro i
  change a.toBasis.repr (b i₀) i = z i
  rw [hb i₀ (Set.mem_singleton i₀)]
  rfl

/-- The normalized constant vector. All its coordinates are nonzero. -/
def uniformVector [Nonempty H] : EuclideanSpace ℂ H :=
  WithLp.toLp 2 (fun _ => (((Real.sqrt (Fintype.card H : ℝ))⁻¹ : ℝ) : ℂ))

omit [DecidableEq H] in
theorem uniformVector_norm [Nonempty H] : ‖uniformVector (H := H)‖ = 1 := by
  have hc : (0 : ℝ) < Fintype.card H := by exact_mod_cast Fintype.card_pos
  have hsq : ‖uniformVector (H := H)‖ ^ 2 = 1 := by
    rw [EuclideanSpace.norm_sq_eq]
    simp only [uniformVector, Complex.norm_real, Real.norm_eq_abs, sq_abs,
      Finset.sum_const, Finset.card_univ, nsmul_eq_mul, inv_pow]
    rw [Real.sq_sqrt hc.le, mul_inv_cancel₀ hc.ne']
  nlinarith [norm_nonneg (uniformVector (H := H))]

omit [DecidableEq H] in
theorem uniformVector_apply_ne_zero [Nonempty H] (i : H) :
    uniformVector (H := H) i ≠ 0 := by
  change (((Real.sqrt (Fintype.card H : ℝ))⁻¹ : ℝ) : ℂ) ≠ 0
  exact_mod_cast inv_ne_zero ((Real.sqrt_pos.mpr
    (show (0 : ℝ) < Fintype.card H by exact_mod_cast Fintype.card_pos)).ne')

/-- A genuine unitary matrix with every entry in a specified column nonzero. -/
theorem exists_unitary_nonzero_column (i₀ : H) :
    ∃ U : Matrix.unitaryGroup H ℂ, ∀ i, (U : Matrix H H ℂ) i i₀ ≠ 0 := by
  letI : Nonempty H := ⟨i₀⟩
  obtain ⟨U, hU⟩ := exists_unitary_column i₀ uniformVector uniformVector_norm
  exact ⟨U, fun i => (hU i) ▸ uniformVector_apply_ne_zero i⟩

end FreeEntropy.UnitaryColumn
