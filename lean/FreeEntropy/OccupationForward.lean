/-
Copyright (c) 2026 Free Entropy formalization contributors.
See LICENSE and NOTICE in the repository root for license and attribution.
-/

import FreeEntropy.OccupationCloning
import FreeEntropy.OccupationDimension

/-!
# Forward pure-state cloning estimate from the concrete splitting matrix

The operator lower bound is proved from the exact factorization under the
constructed isometry. Its trace-distance consequence applies to the actual
normalized Cartan channel once its representation normalization is established.
-/
noncomputable section
open scoped BigOperators Matrix Kronecker ComplexOrder MatrixOrder
open Matrix
namespace FreeEntropy.OccupationCloning
open Occupation OccupationSplit CartanChannel TraceDistance
set_option backward.isDefEq.respectTransparency false
variable {d n m : ℕ}

def dimensionRatio (d n m : ℕ) : ℝ :=
  (Fintype.card (Occupation d n) : ℝ) / (Fintype.card (Occupation d (n + m)) : ℝ)

theorem dimensionRatio_nonneg (d n m : ℕ) : 0 ≤ dimensionRatio d n m := by
  unfold dimensionRatio
  positivity

theorem dimensionRatio_le_one (d n m : ℕ) (hd : 0 < d) : dimensionRatio d n m ≤ 1 := by
  apply (div_le_one (by exact_mod_cast occupationDimension_pos d (n + m) hd)).mpr
  exact_mod_cast (show Fintype.card (Occupation d n) ≤ Fintype.card (Occupation d (n + m)) by
    rw [card_occupation_symm d n hd, card_occupation_symm d (n + m) hd]
    exact Nat.choose_mono (d - 1) (by omega))

/-- The literal forward Cartan formula dominates the target pure state
multiplied by the exact ratio of symmetric-power dimensions. -/
theorem forward_formula_dominates (n m : ℕ) (z : Fin d → ℂ)
    (hz : ∑ i, Complex.normSq (z i) = 1) :
    dimensionRatio d n m • state (n + m) z ≤
      sectorMap (Fintype.card (Occupation d n)) (Fintype.card (Occupation d (n + m)))
        split (state n z) := by
  have hy := OrbitMemory.state_le_one (state_positive m z) (state_trace m z hz)
  have ht : (state n z ⊗ₖ (1 : Matrix (Occupation d m) (Occupation d m) ℂ) -
      state n z ⊗ₖ state m z).PosSemidef := by
    convert (state_positive n z).kronecker (Matrix.le_iff.mp hy) using 1
    ext ⟨a, b⟩ ⟨c, e⟩
    simp [mul_sub]
  have he : (split (d := d) (n := n) (m := m))ᴴ * (state n z ⊗ₖ state m z) * split =
      state (n + m) z := by
    rw [show state n z ⊗ₖ state m z = split * state (n + m) z * splitᴴ from (split_pure z).symm]
    calc
      _ = (splitᴴ * split) * state (n + m) z * (splitᴴ * split) := by
        simp only [Matrix.mul_assoc]
      _ = _ := by rw [split_isometry, Matrix.one_mul, Matrix.mul_one]
  have hp := ht.conjTranspose_mul_mul_same (split (d := d) (n := n) (m := m))
  rw [Matrix.mul_sub, Matrix.sub_mul, he] at hp
  have hps := hp.smul (dimensionRatio_nonneg d n m)
  apply Matrix.le_iff.mpr
  simpa only [sectorMap, ← smul_sub, dimensionRatio] using hps

/-- The exact dimension ratio controls forward error for a CPTP channel
having the constructed Cartan formula. -/
theorem forward_error_of_formula (hd : 0 < d)
    (F : Channels.MatrixChannel (Occupation d n) (Occupation d (n + m)))
    (hF : ∀ X, F.toFun X = sectorMap (Fintype.card (Occupation d n))
      (Fintype.card (Occupation d (n + m))) split X)
    (z : Fin d → ℂ) (hz : ∑ i, Complex.normSq (z i) = 1) :
    traceDistance (F.toFun (state n z)) (state (n + m) z) ≤ 1 - dimensionRatio d n m := by
  have ht : (F.toFun (state n z)).trace = (state (n + m) z).trace := by
    rw [F.trace_preserving, state_trace n z hz, state_trace (n + m) z hz]
  have hR := (state_positive (n + m) z).smul (sub_nonneg.mpr (dimensionRatio_le_one d n m hd))
  have hle : state (n + m) z - (1 - dimensionRatio d n m) • state (n + m) z ≤
      F.toFun (state n z) := by
    rw [hF]
    have heq : state (n + m) z - (1 - dimensionRatio d n m) • state (n + m) z =
        dimensionRatio d n m • state (n + m) z := by module
    rw [heq]
    exact forward_formula_dominates n m z hz
  have he := traceDistance_le_remainder ht hR hle
  simpa only [OrbitMemory.tr, Matrix.trace_smul, state_trace (n + m) z hz,
    Complex.real_smul, mul_one, Complex.ofReal_re] using he

end FreeEntropy.OccupationCloning
