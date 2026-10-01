/-
Copyright (c) 2026 Free Entropy formalization contributors.
See LICENSE and NOTICE in the repository root for license and attribution.
-/

import FreeEntropy.ExteriorCartanEmbedding
import Mathlib.LinearAlgebra.Matrix.Swap
import Mathlib.LinearAlgebra.Matrix.Transvection

/-! Unitary-invariant exterior tensor spaces are preserved by all real matrix
actions. The extension is proved by torus separation, the spectral theorem,
and diagonal/transvection elimination; no complexification assumption is used. -/
noncomputable section
open Matrix
open scoped BigOperators
namespace FreeEntropy.ExteriorRepresentation
open UnitaryDecomposition
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
set_option linter.unusedSectionVars false

variable {d : ℕ} {I : Type*} [Fintype I] [DecidableEq I] (height : I → ℕ)

def ExteriorCommutant (P : Matrix (TensorIndex (d := d) height) (TensorIndex (d := d) height) ℂ) : Prop :=
  ∀ U : Matrix.unitaryGroup (Fin d) ℂ,
    P * tensorMatrix height U.val = tensorMatrix height U.val * P

theorem ExteriorCommutant.entry_eq_zero
    {P : Matrix (TensorIndex (d := d) height) (TensorIndex (d := d) height) ℂ}
    (hP : ExteriorCommutant height P) (x y : TensorIndex (d := d) height)
    (hxy : tensorWeight height x ≠ tensorWeight height y) : P x y = 0 := by
  obtain ⟨z, hz, hchar⟩ := TorusWeights.character_separates
    (tensorWeight height x) (tensorWeight height y) hxy
  have h := congrArg (fun M => M x y) (hP (Occupation.diagonalUnitary z hz))
  change (P * tensorMatrix height (diagonal z)) x y =
    (tensorMatrix height (diagonal z) * P) x y at h
  rw [tensorMatrix_diagonal, Matrix.mul_diagonal, Matrix.diagonal_mul] at h
  change P x y * TorusWeights.character z (tensorWeight height y) =
    TorusWeights.character z (tensorWeight height x) * P x y at h
  have hz' : P x y * (TorusWeights.character z (tensorWeight height y) -
      TorusWeights.character z (tensorWeight height x)) = 0 := by
    rw [mul_sub, h, mul_comm (TorusWeights.character z (tensorWeight height x)), sub_self]
  exact (mul_eq_zero.mp hz').resolve_right (sub_ne_zero.mpr hchar.symm)

theorem ExteriorCommutant.diagonal
    {P : Matrix (TensorIndex (d := d) height) (TensorIndex (d := d) height) ℂ}
    (hP : ExteriorCommutant height P) (z : Fin d → ℂ) :
    P * tensorMatrix height (diagonal z) = tensorMatrix height (diagonal z) * P := by
  rw [tensorMatrix_diagonal]
  ext x y
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
  by_cases hxy : tensorWeight height x = tensorWeight height y
  · rw [hxy]; exact mul_comm _ _
  · rw [hP.entry_eq_zero height x y hxy, zero_mul, mul_zero]

theorem ExteriorCommutant.hermitian
    {P : Matrix (TensorIndex (d := d) height) (TensorIndex (d := d) height) ℂ}
    (hP : ExteriorCommutant height P) {A : Matrix (Fin d) (Fin d) ℂ} (hA : A.IsHermitian) :
    P * tensorMatrix height A = tensorMatrix height A * P := by
  let U := hA.eigenvectorUnitary
  have hs : A = U.val * Matrix.diagonal (fun i => (hA.eigenvalues i : ℂ)) * U.valᴴ := by
    simpa only [U, Unitary.conjStarAlgAut_apply, Matrix.star_eq_conjTranspose,
      Function.comp_def] using hA.spectral_theorem
  rw [hs, tensorMatrix_mul, tensorMatrix_mul, tensorMatrix_adjoint]
  have hU : Commute P (tensorMatrix height U.val) := hP U
  have hD : Commute P (tensorMatrix height (Matrix.diagonal (fun i => (hA.eigenvalues i : ℂ)))) :=
    hP.diagonal height _
  have hUs : Commute P ((tensorMatrix height U.val)ᴴ) := by
    rw [← tensorMatrix_adjoint]
    exact hP (star U)
  exact (hU.mul_right hD).mul_right hUs

/-- A real elementary shear is a product of two actual Hermitian matrices. -/
theorem real_transvection_factor (i j : Fin d) (t : ℝ) :
    transvection i j (t : ℂ) = (Matrix.swap ℂ i j + Matrix.single i i (t : ℂ)) * Matrix.swap ℂ i j := by
  rw [Matrix.add_mul, Matrix.swap_mul_self, transvection]
  congr 1
  ext a b
  by_cases hb : b = j
  · subst b
    simp [Matrix.mul_swap_apply_right, Matrix.single_apply]
  · by_cases hb' : b = i
    · subst b
      simp [Matrix.mul_swap_apply_left, Matrix.single_apply, hb, Ne.symm hb]
    · rw [Matrix.mul_swap_of_ne hb' hb]
      simp [Matrix.single_apply, hb, hb', Ne.symm hb, Ne.symm hb']

theorem ExteriorCommutant.real_transvection
    {P : Matrix (TensorIndex (d := d) height) (TensorIndex (d := d) height) ℂ}
    (hP : ExteriorCommutant height P) (i j : Fin d) (t : ℝ) :
    P * tensorMatrix height (transvection i j (t : ℂ)) =
      tensorMatrix height (transvection i j (t : ℂ)) * P := by
  rw [real_transvection_factor, tensorMatrix_mul]
  apply Commute.mul_right
  · apply hP.hermitian height
    change (_ + _)ᴴ = _
    simp
  · apply hP.hermitian height
    change (Matrix.swap ℂ i j)ᴴ = _
    simp

/-- A nonzero complex shear is a diagonal conjugate of a real unit shear. -/
theorem transvection_diagonal_conjugate (i j : Fin d) (hij : i ≠ j) (c : ℂ) (hc : c ≠ 0) :
    transvection i j c =
      diagonal (fun k => if k = i then c else 1) * transvection i j (1 : ℂ) *
        diagonal (fun k => if k = i then c⁻¹ else 1) := by
  ext a b
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
  by_cases ha : a = i <;> by_cases hb : b = i <;> by_cases hj : b = j <;>
    by_cases hab : a = b <;>
    simp_all [transvection, Matrix.add_apply, Matrix.one_apply, Matrix.single_apply, eq_comm]

theorem ExteriorCommutant.transvection
    {P : Matrix (TensorIndex (d := d) height) (TensorIndex (d := d) height) ℂ}
    (hP : ExteriorCommutant height P) (i j : Fin d) (hij : i ≠ j) (c : ℂ) :
    P * tensorMatrix height (transvection i j c) =
      tensorMatrix height (transvection i j c) * P := by
  by_cases hc : c = 0
  · simp [hc, tensorMatrix_one]
  · rw [transvection_diagonal_conjugate i j hij c hc, tensorMatrix_mul, tensorMatrix_mul]
    apply Commute.mul_right
    · apply Commute.mul_right
      · exact hP.diagonal height _
      · simpa using hP.real_transvection height i j 1
    · exact hP.diagonal height _

/-- The genuine unitary commutant commutes with the polynomial action of
absolutely every complex matrix, including singular matrices. -/
theorem ExteriorCommutant.all_matrix
    {P : Matrix (TensorIndex (d := d) height) (TensorIndex (d := d) height) ℂ}
    (hP : ExteriorCommutant height P) (A : Matrix (Fin d) (Fin d) ℂ) :
    P * tensorMatrix height A = tensorMatrix height A * P := by
  apply Matrix.diagonal_transvection_induction
    (fun A : Matrix (Fin d) (Fin d) ℂ => Commute P (tensorMatrix height A)) A
  · intro z _; exact hP.diagonal height z
  · intro t; exact hP.transvection height t.i t.j t.hij t.c
  · intro A B hA hB
    rw [tensorMatrix_mul]
    exact hA.mul_right hB

/-- Gaussian elimination upgrades genuine unitary commutation to the action
of every real matrix, including singular matrices. -/
theorem ExteriorCommutant.real_matrix
    {P : Matrix (TensorIndex (d := d) height) (TensorIndex (d := d) height) ℂ}
    (hP : ExteriorCommutant height P) (A : Matrix (Fin d) (Fin d) ℝ) :
    P * tensorMatrix height (A.map Complex.ofReal) =
      tensorMatrix height (A.map Complex.ofReal) * P := by
  exact hP.all_matrix height (A.map Complex.ofReal)

variable (mu : Fin d → ℕ)

theorem irrepProjection_commutant :
    ExteriorCommutant (columnHeight mu) (irrepEmbedding mu * (irrepEmbedding mu)ᴴ) :=
  intertwiner_range_projection_commutes (ambientRepresentation mu) (irrepMatrix mu)
    (ambientRepresentation_unitary mu) (irrepMatrix_unitary mu)
    (irrepEmbedding mu) (irrepEmbedding_intertwines mu)

/-- Every complex polynomial orbit vector belongs to the actual canonical
irreducible unitary space. -/
theorem matrix_highest_mem (A : Matrix (Fin d) (Fin d) ℂ) :
    Matrix.toEuclideanLin (tensorMatrix (columnHeight mu) A) (highestVector mu) ∈
      highestSubspace mu := by
  apply Submodule.starProjection_eq_self_iff.mp
  rw [← embedding_projection]
  apply WithLp.ofLp_injective 2
  change (irrepEmbedding mu * (irrepEmbedding mu)ᴴ) *ᵥ
    (tensorMatrix (columnHeight mu) A *ᵥ Pi.single (highestBasisIndex mu) 1) = _
  rw [Matrix.mulVec_mulVec, (irrepProjection_commutant mu).all_matrix (columnHeight mu) A,
    ← Matrix.mulVec_mulVec, irrepProjection_highest]
  rfl

/-- The actual canonical irreducible space contains the real-matrix orbit of
its highest vector; this is not an assumed polynomial-representation extension. -/
theorem real_matrix_highest_mem (A : Matrix (Fin d) (Fin d) ℝ) :
    Matrix.toEuclideanLin (tensorMatrix (columnHeight mu) (A.map Complex.ofReal)) (highestVector mu) ∈
      highestSubspace mu := by
  apply Submodule.starProjection_eq_self_iff.mp
  rw [← embedding_projection]
  apply WithLp.ofLp_injective 2
  change (irrepEmbedding mu * (irrepEmbedding mu)ᴴ) *ᵥ
    (tensorMatrix (columnHeight mu) (A.map Complex.ofReal) *ᵥ Pi.single (highestBasisIndex mu) 1) = _
  rw [Matrix.mulVec_mulVec, (irrepProjection_commutant mu).real_matrix (columnHeight mu) A,
    ← Matrix.mulVec_mulVec, irrepProjection_highest]
  rfl

end FreeEntropy.ExteriorRepresentation
