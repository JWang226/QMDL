/-
Copyright (c) 2026 Free Entropy formalization contributors.
See LICENSE and NOTICE in the repository root for license and attribution.
-/

import FreeEntropy.ExteriorCartanEmbedding
import FreeEntropy.CartanBalance

/-! Actual completely positive trace-preserving Cartan channels for the
canonically constructed polynomial irreducible unitary representations. -/
noncomputable section
open Matrix
open scoped Kronecker
namespace FreeEntropy.ExteriorRepresentation
set_option backward.isDefEq.respectTransparency false

variable {d : ℕ} (mu nu : Fin d → ℕ) (hmu : Antitone mu) (hnu : Antitone nu)

local instance irrepIndex_nonempty (lam : Fin d → ℕ) : Nonempty (IrrepIndex lam) :=
  Fin.pos_iff_nonempty.mp (irrep_dimension_pos lam)

/-- The exact partial-trace balance of the canonical Cartan isometry. -/
theorem cartanEmbedding_balance :
    CartanChannel.partialTrace
      (cartanEmbedding mu nu hmu hnu * (cartanEmbedding mu nu hmu hnu)ᴴ) =
      ((Fintype.card (IrrepIndex (mu + nu)) : ℝ) / (Fintype.card (IrrepIndex mu) : ℝ)) •
        (1 : Matrix (IrrepIndex mu) (IrrepIndex mu) ℂ) := by
  letI := irrepMatrix_irreducible mu
  exact CartanBalance.balance_of_irreducible (irrepMatrix mu) (irrepMatrix nu)
    (irrepMatrix (mu + nu)) (irrepMatrix_unitary mu) (irrepMatrix_unitary nu)
    (irrepMatrix_unitary (mu + nu)) (cartanEmbedding mu nu hmu hnu)
    (cartanEmbedding_isometry mu nu hmu hnu) (cartanEmbedding_intertwines mu nu hmu hnu)

/-- The forward Cartan cloning channel exists for every pair of dominant rows,
with all representation, isometry, irreducibility, and normalization inputs constructed. -/
def forwardCartanChannel : Channels.MatrixChannel (IrrepIndex mu) (IrrepIndex (mu + nu)) :=
  CartanChannel.cartanChannel (cartanEmbedding mu nu hmu hnu)
    (Fintype.card (IrrepIndex mu)) (Fintype.card (IrrepIndex (mu + nu)))
    (by exact_mod_cast Fintype.card_pos (α := IrrepIndex mu))
    (by exact_mod_cast Fintype.card_pos (α := IrrepIndex (mu + nu)))
    (cartanEmbedding_balance mu nu hmu hnu)

/-- The reverse channel is the actual isometric inclusion followed by partial trace. -/
def reverseCartanChannel : Channels.MatrixChannel (IrrepIndex (mu + nu)) (IrrepIndex mu) :=
  CartanChannel.reverseChannel (cartanEmbedding mu nu hmu hnu)
    (cartanEmbedding_isometry mu nu hmu hnu)

theorem forwardCartanChannel_apply (X : Matrix (IrrepIndex mu) (IrrepIndex mu) ℂ) :
    (forwardCartanChannel mu nu hmu hnu).toFun X =
      ((Fintype.card (IrrepIndex mu) : ℝ) / (Fintype.card (IrrepIndex (mu + nu)) : ℝ)) •
        ((cartanEmbedding mu nu hmu hnu)ᴴ * (X ⊗ₖ (1 : Matrix (IrrepIndex nu) (IrrepIndex nu) ℂ)) *
          cartanEmbedding mu nu hmu hnu) :=
  CartanChannel.cartanChannel_apply _ _ _ _ _ _ X

theorem reverseCartanChannel_apply
    (Y : Matrix (IrrepIndex (mu + nu)) (IrrepIndex (mu + nu)) ℂ) :
    (reverseCartanChannel mu nu hmu hnu).toFun Y =
      CartanChannel.partialTrace
        (cartanEmbedding mu nu hmu hnu * Y * (cartanEmbedding mu nu hmu hnu)ᴴ) :=
  CartanChannel.reverseChannel_apply _ _ Y

end FreeEntropy.ExteriorRepresentation
