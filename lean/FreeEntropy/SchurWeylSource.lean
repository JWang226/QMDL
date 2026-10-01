/-
Copyright (c) 2026 Free Entropy formalization contributors.
See LICENSE and NOTICE in the repository root for license and attribution.
-/

import FreeEntropy.OccupationTorus
import FreeEntropy.TensorPowers

/-!
# The genuine mixed tensor-power source belongs to the unitary bicommutant

An operator commuting with all tensor powers of physical unitaries cannot
connect distinct word-content weights: diagonal phases separate those weights.
It therefore commutes with every diagonal tensor power. The spectral theorem
then proves that it commutes with every Hermitian tensor-power source.

This is the source-identification bridge needed by a complete unitary
irreducible decomposition: invariant orthogonal projections reduce the
source, and intertwiners between equivalent copies also intertwine their
source blocks. No Schur decomposition or source block formula is assumed.
-/
noncomputable section
open scoped BigOperators ComplexOrder MatrixOrder
open Matrix
namespace FreeEntropy.SchurWeyl
open WordTypes Occupation
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
variable {d n : ℕ}

/-- Commutation with the actual tensor-power action of the physical U(d). -/
def TensorCommutant (T : Matrix (Fin n → Fin d) (Fin n → Fin d) ℂ) : Prop :=
  ∀ U : Matrix.unitaryGroup (Fin d) ℂ,
    T * TensorPowers.matrix n U.val = TensorPowers.matrix n U.val * T

theorem tensorVector_eq_character (z : Fin d → ℂ) (w : Fin n → Fin d) :
    TensorPowers.vector n z w = character z (ofWord w) := by
  simpa only [TensorPowers.vector, character, ofWord, content, Finset.prod_const] using
    (Finset.prod_fiberwise' Finset.univ w z).symm

/-- Distinct tensor weights cannot be coupled by an operator in the genuine
unitary commutant. -/
theorem TensorCommutant.entry_eq_zero {T : Matrix (Fin n → Fin d) (Fin n → Fin d) ℂ}
    (hT : TensorCommutant T) (x y : Fin n → Fin d) (hxy : content x ≠ content y) :
    T x y = 0 := by
  have hocc : ofWord x ≠ ofWord y := fun h => hxy (congrArg Subtype.val h)
  obtain ⟨z, hz, hchar⟩ := character_separates (ofWord x) (ofWord y) hocc
  have h := congrArg (fun M => M x y) (hT (diagonalUnitary z hz))
  change (T * TensorPowers.matrix n (diagonal z)) x y =
    (TensorPowers.matrix n (diagonal z) * T) x y at h
  rw [tensor_diagonal, Matrix.mul_diagonal, Matrix.diagonal_mul,
    tensorVector_eq_character, tensorVector_eq_character] at h
  have hz' : T x y * (character z (ofWord y) - character z (ofWord x)) = 0 := by
    rw [mul_sub, h, mul_comm (character z (ofWord x)), sub_self]
  exact (mul_eq_zero.mp hz').resolve_right (sub_ne_zero.mpr hchar.symm)

/-- The actual unitary commutant commutes with every diagonal tensor power,
with arbitrary complex diagonal entries. -/
theorem TensorCommutant.diagonal {T : Matrix (Fin n → Fin d) (Fin n → Fin d) ℂ}
    (hT : TensorCommutant T) (z : Fin d → ℂ) :
    T * TensorPowers.matrix n (diagonal z) = TensorPowers.matrix n (diagonal z) * T := by
  rw [tensor_diagonal]
  ext x y
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
  by_cases hxy : content x = content y
  · rw [(tensor_vector_contentInvariant z) x y hxy]
    exact mul_comm _ _
  · rw [hT.entry_eq_zero x y hxy, zero_mul, mul_zero]

/-- The physical mixed-state tensor power lies in the bicommutant of the
actual tensor-power unitary representation. Hermiticity alone suffices. -/
theorem TensorCommutant.hermitian {T : Matrix (Fin n → Fin d) (Fin n → Fin d) ℂ}
    (hT : TensorCommutant T) {A : Matrix (Fin d) (Fin d) ℂ} (hA : A.IsHermitian) :
    T * TensorPowers.matrix n A = TensorPowers.matrix n A * T := by
  let U := hA.eigenvectorUnitary
  have hs : A = U.val * Matrix.diagonal (fun i => (hA.eigenvalues i : ℂ)) * U.valᴴ := by
    simpa only [U, Unitary.conjStarAlgAut_apply, Matrix.star_eq_conjTranspose,
      Function.comp_def] using hA.spectral_theorem
  rw [hs, TensorPowers.matrix_covariance]
  have hU : Commute T (TensorPowers.matrix n U.val) := hT U
  have hD : Commute T (TensorPowers.matrix n (Matrix.diagonal (fun i => (hA.eigenvalues i : ℂ)))) :=
    hT.diagonal _
  have hUs : Commute T ((TensorPowers.matrix n U.val)ᴴ) := by
    rw [← TensorPowers.matrix_adjoint]
    exact hT (star U)
  exact (hU.mul_right hD).mul_right hUs

/-- Density matrices are an immediate specialization, with no assumed
mixed-state Schur–Weyl identity. -/
theorem TensorCommutant.positive {T : Matrix (Fin n → Fin d) (Fin n → Fin d) ℂ}
    (hT : TensorCommutant T) {ρ : Matrix (Fin d) (Fin d) ℂ} (hρ : ρ.PosSemidef) :
    T * TensorPowers.matrix n ρ = TensorPowers.matrix n ρ * T :=
  hT.hermitian hρ.isHermitian

end FreeEntropy.SchurWeyl
