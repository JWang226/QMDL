/-
Copyright (c) 2026 Free Entropy formalization contributors.
See LICENSE and NOTICE in the repository root for license and attribution.
-/

import FreeEntropy.TensorSites
import FreeEntropy.TorusWeightEigenline

/-! A genuine torus intertwiner automatically intertwines the diagonal
matrix Lie generators with its integral coordinate weights. -/
noncomputable section
open Matrix
namespace FreeEntropy.SchurWeyl
set_option backward.isDefEq.respectTransparency false
variable {d n : ℕ} {B : Type*} [Fintype B] [DecidableEq B]

theorem torus_intertwiner_support (J : Matrix (Fin n → Fin d) B ℂ)
    (weight : B → Fin d → ℕ)
    (hJ : ∀ z : Fin d → ℂ, (∀ i, ‖z i‖ = 1) →
      TensorPowers.matrix n (diagonal z) * J =
        J * diagonal (fun b => TorusWeights.character z (weight b)))
    (w : Fin n → Fin d) (b : B) (hwb : WordTypes.content w ≠ weight b) : J w b = 0 := by
  obtain ⟨z, hz, hchar⟩ := TorusWeights.character_separates (WordTypes.content w) (weight b) hwb
  have h := congrArg (fun M => M w b) (hJ z hz)
  dsimp only at h
  rw [Occupation.tensor_diagonal, Matrix.diagonal_mul, Matrix.mul_diagonal,
    tensorVector_eq_character] at h
  change TorusWeights.character z (WordTypes.content w) * J w b =
    J w b * TorusWeights.character z (weight b) at h
  have hp : (TorusWeights.character z (WordTypes.content w) -
      TorusWeights.character z (weight b)) * J w b = 0 := by
    rw [sub_mul, h, mul_comm (TorusWeights.character z (weight b)), sub_self]
  exact (mul_eq_zero.mp hp).resolve_left (sub_ne_zero.mpr hchar)

/-- Integral torus weights are the actual diagonal Lie eigenvalues. -/
theorem diagonal_intertwines_of_torus (J : Matrix (Fin n → Fin d) B ℂ)
    (weight : B → Fin d → ℕ)
    (hJ : ∀ z : Fin d → ℂ, (∀ i, ‖z i‖ = 1) →
      TensorPowers.matrix n (diagonal z) * J =
        J * diagonal (fun b => TorusWeights.character z (weight b))) (k : Fin d) :
    (TensorPowers.generators d n).E k k * J =
      J * diagonal (fun b => (weight b k : ℂ)) := by
  rw [TensorPowers.generators_diagonal]
  ext w b
  simp only [Matrix.diagonal_mul, Matrix.mul_diagonal]
  by_cases hwb : WordTypes.content w = weight b
  · rw [hwb, mul_comm]
  · rw [torus_intertwiner_support J weight hJ w b hwb, mul_zero, zero_mul]

end FreeEntropy.SchurWeyl
