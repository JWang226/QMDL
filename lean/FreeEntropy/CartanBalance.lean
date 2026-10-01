/-
Copyright (c) 2026 Free Entropy formalization contributors.
See LICENSE and NOTICE in the repository root for license and attribution.
-/

import FreeEntropy.CartanChannel
import FreeEntropy.Twirling

/-!
# Cartan-channel normalization from genuine irreducibility

An isometric intertwiner into a tensor product gives the required partial
trace balance. The proof uses the proved partial-trace covariance and the
matrix Schur lemma for Mathlib's actual irreducibility class. Scalarity and
the balance identity are conclusions, not hypotheses.
-/

noncomputable section
open Matrix
open scoped Kronecker

namespace FreeEntropy.CartanBalance

open CartanChannel

set_option backward.isDefEq.respectTransparency false

variable {G A B C : Type*} [Group G]
  [Fintype A] [Fintype B] [Fintype C]
  [DecidableEq A] [DecidableEq B] [DecidableEq C]

/-- The partial trace of an invariant range projection commutes with the
input representation. No topological hypothesis is necessary. -/
theorem partialTrace_range_commutes
    (U : G →* Matrix A A ℂ) (W : G →* Matrix B B ℂ) (Z : G →* Matrix C C ℂ)
    (hU : ∀ g, (U g)ᴴ * U g = 1)
    (hW : ∀ g, (W g)ᴴ * W g = 1)
    (hZ : ∀ g, (Z g)ᴴ * Z g = 1)
    (V : Matrix (A × B) C ℂ)
    (hintertwine : ∀ g, (U g ⊗ₖ W g) * V = V * Z g) (g : G) :
    partialTrace (V * Vᴴ) * U g = U g * partialTrace (V * Vᴴ) := by
  have hZright : Z g * (Z g)ᴴ = 1 := mul_eq_one_comm.mp (hZ g)
  have hc := reverseMap_covariant (U g) (W g) (Z g) V (hW g) (hintertwine g) 1
  simp only [Matrix.mul_one, hZright, reverseMap] at hc
  have hm := congrArg (fun X => X * U g) hc
  simpa only [Matrix.mul_assoc, hU g, Matrix.mul_one] using hm

/-- Actual representation irreducibility forces the partial trace scalar. -/
theorem partialTrace_range_scalar
    (U : G →* Matrix A A ℂ) (W : G →* Matrix B B ℂ) (Z : G →* Matrix C C ℂ)
    [Representation.IsIrreducible (Twirling.matrixRepresentation U)]
    (hU : ∀ g, (U g)ᴴ * U g = 1)
    (hW : ∀ g, (W g)ᴴ * W g = 1)
    (hZ : ∀ g, (Z g)ᴴ * Z g = 1)
    (V : Matrix (A × B) C ℂ)
    (hintertwine : ∀ g, (U g ⊗ₖ W g) * V = V * Z g) :
    ∃ c : ℂ, partialTrace (V * Vᴴ) = c • (1 : Matrix A A ℂ) :=
  Twirling.commutant_is_scalar U (partialTrace (V * Vᴴ))
    (partialTrace_range_commutes U W Z hU hW hZ V hintertwine)

/-- The exact dimension balance required for trace preservation follows
from a genuine irreducible unitary representation and isometric intertwiner. -/
theorem balance_of_irreducible [Nonempty A]
    (U : G →* Matrix A A ℂ) (W : G →* Matrix B B ℂ) (Z : G →* Matrix C C ℂ)
    [Representation.IsIrreducible (Twirling.matrixRepresentation U)]
    (hU : ∀ g, (U g)ᴴ * U g = 1)
    (hW : ∀ g, (W g)ᴴ * W g = 1)
    (hZ : ∀ g, (Z g)ᴴ * Z g = 1)
    (V : Matrix (A × B) C ℂ) (hV : Vᴴ * V = 1)
    (hintertwine : ∀ g, (U g ⊗ₖ W g) * V = V * Z g) :
    partialTrace (V * Vᴴ) =
      ((Fintype.card C : ℝ) / (Fintype.card A : ℝ)) • (1 : Matrix A A ℂ) := by
  obtain ⟨c, hc⟩ := partialTrace_range_scalar U W Z hU hW hZ V hintertwine
  have ht := congrArg Matrix.trace hc
  rw [trace_partialTrace, Matrix.trace_mul_comm V, hV] at ht
  simp only [Matrix.trace_one, Matrix.trace_smul, smul_eq_mul] at ht
  have him := congrArg Complex.im ht
  simp only [Complex.natCast_im, Complex.mul_im, Complex.natCast_re,
    mul_zero, zero_add] at him
  have hd : (Fintype.card A : ℝ) ≠ 0 := by
    exact_mod_cast (Fintype.card_ne_zero : Fintype.card A ≠ 0)
  have hcim : c.im = 0 := (mul_eq_zero.mp him.symm).resolve_right hd
  have hreal : (c.re : ℂ) = c := by
    apply Complex.ext <;> simp [hcim]
  have hcR : partialTrace (V * Vᴴ) = c.re • (1 : Matrix A A ℂ) := by
    rw [hc, ← hreal, Complex.coe_smul]
    simp
  exact balance_of_scalar V hV c.re hcR

/-- The actual-dimension Cartan channel, with normalization derived from
irreducibility rather than supplied as a balance/scalarity assumption. -/
def cartanChannelOfIrreducible [Nonempty A] [Nonempty C]
    (U : G →* Matrix A A ℂ) (W : G →* Matrix B B ℂ) (Z : G →* Matrix C C ℂ)
    [Representation.IsIrreducible (Twirling.matrixRepresentation U)]
    (hU : ∀ g, (U g)ᴴ * U g = 1)
    (hW : ∀ g, (W g)ᴴ * W g = 1)
    (hZ : ∀ g, (Z g)ᴴ * Z g = 1)
    (V : Matrix (A × B) C ℂ) (hV : Vᴴ * V = 1)
    (hintertwine : ∀ g, (U g ⊗ₖ W g) * V = V * Z g) :
    Channels.MatrixChannel A C :=
  cartanChannel V (Fintype.card A : ℝ) (Fintype.card C : ℝ)
    (by exact_mod_cast (Fintype.card_pos : 0 < Fintype.card A))
    (by exact_mod_cast (Fintype.card_pos : 0 < Fintype.card C))
    (balance_of_irreducible U W Z hU hW hZ V hV hintertwine)

theorem cartanChannelOfIrreducible_apply [Nonempty A] [Nonempty C]
    (U : G →* Matrix A A ℂ) (W : G →* Matrix B B ℂ) (Z : G →* Matrix C C ℂ)
    [Representation.IsIrreducible (Twirling.matrixRepresentation U)]
    (hU : ∀ g, (U g)ᴴ * U g = 1)
    (hW : ∀ g, (W g)ᴴ * W g = 1)
    (hZ : ∀ g, (Z g)ᴴ * Z g = 1)
    (V : Matrix (A × B) C ℂ) (hV : Vᴴ * V = 1)
    (hintertwine : ∀ g, (U g ⊗ₖ W g) * V = V * Z g) (X : Matrix A A ℂ) :
    (cartanChannelOfIrreducible U W Z hU hW hZ V hV hintertwine).toFun X =
      sectorMap (Fintype.card A : ℝ) (Fintype.card C : ℝ) V X :=
  cartanChannel_apply V _ _ _ _ _ X

end FreeEntropy.CartanBalance
