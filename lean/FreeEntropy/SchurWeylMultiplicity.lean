/-
Copyright (c) 2026 Free Entropy formalization contributors.
See LICENSE and NOTICE in the repository root for license and attribution.
-/

import FreeEntropy.SchurWeylBlocks
import FreeEntropy.MultiplicityChannels

/-!
# The actual identity on a mixed source's multiplicity register

A family of orthogonal copies of the same genuine unitary representation
has a source matrix equal to the common compressed physical source tensored
with the identity on the copy index. The identity factor is derived from
commutant matrix units; it is not a source decomposition hypothesis.
-/
noncomputable section
open scoped BigOperators Kronecker ComplexOrder MatrixOrder
open Matrix
namespace FreeEntropy.SchurWeyl
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
set_option linter.unusedSectionVars false
variable {d n : ℕ}
variable {A M : Type*} [Fintype A] [DecidableEq A] [Fintype M] [DecidableEq M]

/-- Assemble equal representation copies into one explicit multiplicity register. -/
def multiplicityEmbedding (J : M → Matrix (Fin n → Fin d) A ℂ) :
    Matrix (Fin n → Fin d) (A × M) ℂ := fun w am => J am.2 w am.1

theorem multiplicityEmbedding_isometry
    (J : M → Matrix (Fin n → Fin d) A ℂ) (hJ : ∀ a, (J a)ᴴ * J a = 1)
    (horth : ∀ a b, a ≠ b → (J a)ᴴ * J b = 0) :
    (multiplicityEmbedding J)ᴴ * multiplicityEmbedding J = 1 := by
  ext ⟨a, i⟩ ⟨b, j⟩
  change ((J i)ᴴ * J j) a b = _
  by_cases hij : i = j
  · subst j
    rw [hJ i]
    simp [Matrix.one_apply]
  · rw [horth i j hij]
    simp [hij]

theorem multiplicityEmbedding_compression_entry
    (J : M → Matrix (Fin n → Fin d) A ℂ)
    (X : Matrix (Fin n → Fin d) (Fin n → Fin d) ℂ) (a b : A) (i j : M) :
    ((multiplicityEmbedding J)ᴴ * X * multiplicityEmbedding J) (a, i) (b, j) =
      ((J i)ᴴ * X * J j) a b := rfl

/-- Literal multiplicity-identity block formula for every Hermitian physical
source, derived from genuine intertwining and orthogonality. -/
theorem source_multiplicity_identity
    (R : Matrix.unitaryGroup (Fin d) ℂ →* Matrix A A ℂ)
    (J : M → Matrix (Fin n → Fin d) A ℂ) (i₀ : M)
    (hJ : ∀ a, (J a)ᴴ * J a = 1)
    (horth : ∀ a b, a ≠ b → (J a)ᴴ * J b = 0)
    (hJR : ∀ a U, physicalRepresentation d n U * J a = J a * R U)
    {ρ : Matrix (Fin d) (Fin d) ℂ} (hρ : ρ.IsHermitian) :
    (multiplicityEmbedding J)ᴴ * TensorPowers.matrix n ρ * multiplicityEmbedding J =
      ((J i₀)ᴴ * TensorPowers.matrix n ρ * J i₀) ⊗ₖ (1 : Matrix M M ℂ) := by
  ext ⟨a, i⟩ ⟨b, j⟩
  rw [multiplicityEmbedding_compression_entry, Matrix.kronecker_apply]
  by_cases hij : i = j
  · subst j
    rw [Matrix.one_apply_eq, mul_one,
      source_blocks_equal R (J i) (J i₀) (hJ i) (hJ i₀) (hJR i) (hJR i₀) hρ]
  · rw [Matrix.one_apply_ne hij, mul_zero,
      source_crossBlock_zero R (J i) (J j) (hJ j) (horth i j hij) (hJR j) hρ]
    rfl

/-- The common source block is positive for every actual density source. -/
theorem source_compressed_positive (J : Matrix (Fin n → Fin d) A ℂ)
    {ρ : Matrix (Fin d) (Fin d) ℂ} (hρ : ρ.PosSemidef) :
    (Jᴴ * TensorPowers.matrix n ρ * J).PosSemidef :=
  (TensorPowers.matrix_positive n hρ).conjTranspose_mul_mul_same J

end FreeEntropy.SchurWeyl
