/-
Copyright (c) 2026 Free Entropy formalization contributors.
See LICENSE and NOTICE in the repository root for license and attribution.
-/

import FreeEntropy.SchurWeylMultiplicity
import Mathlib.Analysis.Matrix.PosDef

/-!
# Normalizing the derived mixed-state multiplicity blocks

Every positive compressed block, including a zero block, is explicitly
written as its trace mass times a density matrix. Consequently the derived
identity on the copy register becomes a maximally mixed state with the
correct multiplicity-weighted probability. No normalization or probability
formula is assumed.
-/
noncomputable section
open scoped BigOperators Kronecker ComplexOrder MatrixOrder
open Matrix
namespace FreeEntropy.SchurWeyl
open OrbitMemory MultiplicityChannels
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
variable {A M : Type*} [Fintype A] [DecidableEq A] [Nonempty A]
  [Fintype M] [DecidableEq M] [Nonempty M]

/-- Normalize a positive block; the zero block uses a fixed maximally mixed state. -/
def normalizedBlock (B : Matrix A A ℂ) : Matrix A A ℂ :=
  if tr B = 0 then maximallyMixed A else (tr B)⁻¹ • B

theorem positive_trace_real {B : Matrix A A ℂ} (hB : B.PosSemidef) : (tr B : ℂ) = B.trace := by
  apply Complex.ext
  · rfl
  · exact hB.trace_nonneg.2

theorem normalizedBlock_positive {B : Matrix A A ℂ} (hB : B.PosSemidef) :
    (normalizedBlock B).PosSemidef := by
  unfold normalizedBlock
  split_ifs
  · exact maximallyMixed_positive
  · exact hB.smul (inv_nonneg.mpr hB.trace_nonneg.1)

theorem normalizedBlock_trace {B : Matrix A A ℂ} (hB : B.PosSemidef) :
    (normalizedBlock B).trace = 1 := by
  unfold normalizedBlock
  split_ifs with hzero
  · exact maximallyMixed_trace
  · rw [Matrix.trace_smul, ← positive_trace_real hB, Complex.real_smul,
      ← Complex.ofReal_mul, inv_mul_cancel₀ hzero]
    rfl

/-- Exact normalization, valid even for sectors with zero probability. -/
theorem block_eq_trace_smul_normalized {B : Matrix A A ℂ} (hB : B.PosSemidef) :
    B = tr B • normalizedBlock B := by
  by_cases hz : tr B = 0
  · have ht : B.trace = 0 := by rw [← positive_trace_real hB, hz]; rfl
    rw [hz, zero_smul]
    exact hB.trace_eq_zero_iff.mp ht
  · rw [normalizedBlock, if_neg hz, smul_smul, mul_inv_cancel₀ hz, one_smul]

/-- The unnormalized multiplicity identity is exactly a probability mass
times a density block and a maximally mixed multiplicity register. -/
theorem multiplicity_block_normalized {B : Matrix A A ℂ} (hB : B.PosSemidef) :
    B ⊗ₖ (1 : Matrix M M ℂ) =
      ((Fintype.card M : ℝ) * tr B) • (normalizedBlock B ⊗ₖ maximallyMixed M) := by
  have hm : (Fintype.card M : ℝ) ≠ 0 := by exact_mod_cast (Fintype.card_ne_zero : Fintype.card M ≠ 0)
  calc
    _ = (tr B • normalizedBlock B) ⊗ₖ (1 : Matrix M M ℂ) := by
      rw [← block_eq_trace_smul_normalized hB]
    _ = tr B • (normalizedBlock B ⊗ₖ (1 : Matrix M M ℂ)) := by
      rw [Matrix.smul_kronecker]
    _ = _ := by
      rw [maximallyMixed, Matrix.kronecker_smul, smul_smul]
      congr 1
      field_simp

/-- The weight of an isotypic source block is nonnegative. -/
theorem multiplicity_mass_nonneg {B : Matrix A A ℂ} (hB : B.PosSemidef) :
    0 ≤ (Fintype.card M : ℝ) * tr B :=
  mul_nonneg (Nat.cast_nonneg _) hB.trace_nonneg.1

/-- The normalized mixed-state multiplicity formula for the literal
physical tensor-power source follows from representation intertwiners. -/
theorem source_multiplicity_normalized {d n : ℕ}
    (R : Matrix.unitaryGroup (Fin d) ℂ →* Matrix A A ℂ)
    (J : M → Matrix (Fin n → Fin d) A ℂ) (i₀ : M)
    (hJ : ∀ a, (J a)ᴴ * J a = 1)
    (horth : ∀ a b, a ≠ b → (J a)ᴴ * J b = 0)
    (hJR : ∀ a U, physicalRepresentation d n U * J a = J a * R U)
    {ρ : Matrix (Fin d) (Fin d) ℂ} (hρ : ρ.PosSemidef) :
    (multiplicityEmbedding J)ᴴ * TensorPowers.matrix n ρ * multiplicityEmbedding J =
      ((Fintype.card M : ℝ) * tr ((J i₀)ᴴ * TensorPowers.matrix n ρ * J i₀)) •
        (normalizedBlock ((J i₀)ᴴ * TensorPowers.matrix n ρ * J i₀) ⊗ₖ maximallyMixed M) := by
  rw [source_multiplicity_identity R J i₀ hJ horth hJR hρ.isHermitian]
  exact multiplicity_block_normalized (source_compressed_positive (J i₀) hρ)

end FreeEntropy.SchurWeyl
