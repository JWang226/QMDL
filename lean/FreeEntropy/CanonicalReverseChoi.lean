/-
Copyright (c) 2026 Free Entropy formalization contributors.
See LICENSE and NOTICE in the repository root for license and attribution.
-/

import FreeEntropy.ReverseChoi
import FreeEntropy.CanonicalChoi

/-! Literal reverse Choi formula for the constructed canonical Cartan channels.
The reverse support is the conjugate-flipped forward projector. -/
noncomputable section
open Matrix
open scoped BigOperators ComplexOrder MatrixOrder
namespace FreeEntropy.ExteriorRepresentation
open CartanLieCloning CartanChannel CartanChoi
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
variable {d : ℕ}
local instance (mu : Fin d → ℕ) : Nonempty (IrrepIndex mu) :=
  Fin.pos_iff_nonempty.mp (irrep_dimension_pos mu)

def canonicalReverseChoiProjector (mu nu : Fin d → ℕ) (hmu : Antitone mu) (hnu : Antitone nu)
    (hinc : Antitone (fun i => (nu i : ℝ) - (mu i : ℝ))) :
    Matrix (IrrepIndex nu × IrrepIndex mu) (IrrepIndex nu × IrrepIndex mu) ℂ :=
  reverseProjector (specifiedCartanEmbedding (canonicalWeightModel mu) (canonicalAuxiliaryModel mu nu)
    (canonicalWeightModel nu) (canonicalAuxiliaryModel_hrow mu nu hmu hnu hinc))

def canonicalReverseChoiEmbedding (mu nu : Fin d → ℕ) (hmu : Antitone mu) (hnu : Antitone nu)
    (hinc : Antitone (fun i => (nu i : ℝ) - (mu i : ℝ))) :
    Matrix (IrrepIndex nu × IrrepIndex mu) (IrrepIndex (auxiliaryRow mu nu)) ℂ :=
  reverseEmbedding (specifiedCartanEmbedding (canonicalWeightModel mu) (canonicalAuxiliaryModel mu nu)
    (canonicalWeightModel nu) (canonicalAuxiliaryModel_hrow mu nu hmu hnu hinc))

theorem canonicalReverseChoiEmbedding_isometry (mu nu : Fin d → ℕ)
    (hmu : Antitone mu) (hnu : Antitone nu)
    (hinc : Antitone (fun i => (nu i : ℝ) - (mu i : ℝ))) :
    (canonicalReverseChoiEmbedding mu nu hmu hnu hinc)ᴴ * canonicalReverseChoiEmbedding mu nu hmu hnu hinc = 1 :=
  reverseEmbedding_isometry _ _ _ _ (specifiedCartanEmbedding_isometry _ _ _ _)
    (specifiedCartanEmbedding_intertwines _ _ _ _)

theorem canonicalReverseChoiEmbedding_projector (mu nu : Fin d → ℕ)
    (hmu : Antitone mu) (hnu : Antitone nu)
    (hinc : Antitone (fun i => (nu i : ℝ) - (mu i : ℝ))) :
    canonicalReverseChoiEmbedding mu nu hmu hnu hinc * (canonicalReverseChoiEmbedding mu nu hmu hnu hinc)ᴴ =
      canonicalReverseChoiProjector mu nu hmu hnu hinc := reverseEmbedding_projector _

theorem canonicalReverseChoiProjector_hermitian (mu nu : Fin d → ℕ)
    (hmu : Antitone mu) (hnu : Antitone nu)
    (hinc : Antitone (fun i => (nu i : ℝ) - (mu i : ℝ))) :
    (canonicalReverseChoiProjector mu nu hmu hnu hinc).IsHermitian := reverseProjector_hermitian _

theorem canonicalReverseChoiProjector_idempotent (mu nu : Fin d → ℕ)
    (hmu : Antitone mu) (hnu : Antitone nu)
    (hinc : Antitone (fun i => (nu i : ℝ) - (mu i : ℝ))) :
    canonicalReverseChoiProjector mu nu hmu hnu hinc * canonicalReverseChoiProjector mu nu hmu hnu hinc =
      canonicalReverseChoiProjector mu nu hmu hnu hinc :=
  reverseProjector_idempotent _ _ _ _ (specifiedCartanEmbedding_isometry _ _ _ _)
    (specifiedCartanEmbedding_intertwines _ _ _ _)

theorem canonicalReverseChoiProjector_rank (mu nu : Fin d → ℕ)
    (hmu : Antitone mu) (hnu : Antitone nu)
    (hinc : Antitone (fun i => (nu i : ℝ) - (mu i : ℝ))) :
    (canonicalReverseChoiProjector mu nu hmu hnu hinc).rank =
      Fintype.card (IrrepIndex (auxiliaryRow mu nu)) :=
  reverseProjector_rank _ _ _ _ (specifiedCartanEmbedding_isometry _ _ _ _)
    (specifiedCartanEmbedding_intertwines _ _ _ _)

theorem canonicalReverseChoiProjector_eq_flip (mu nu : Fin d → ℕ)
    (hmu : Antitone mu) (hnu : Antitone nu)
    (hinc : Antitone (fun i => (nu i : ℝ) - (mu i : ℝ))) :
    canonicalReverseChoiProjector mu nu hmu hnu hinc =
      flipConjugate (canonicalChoiProjector mu nu hmu hnu hinc) := rfl

theorem canonicalReverseChoiProjector_positive (mu nu : Fin d → ℕ)
    (hmu : Antitone mu) (hnu : Antitone nu)
    (hinc : Antitone (fun i => (nu i : ℝ) - (mu i : ℝ))) :
    (canonicalReverseChoiProjector mu nu hmu hnu hinc).PosSemidef :=
  reverseProjector_positive _

/-- The Choi matrix of the literal reverse cloner, including the zero-increment case. -/
theorem canonicalReverse_choi (mu nu : Fin d → ℕ)
    (hmu : Antitone mu) (hnu : Antitone nu)
    (hinc : Antitone (fun i => (nu i : ℝ) - (mu i : ℝ))) (hd : 0 < d) :
    choi (canonicalReverse mu nu hmu hnu hinc).toFun =
      ((Fintype.card (IrrepIndex nu) : ℝ) / Fintype.card (IrrepIndex (auxiliaryRow mu nu))) •
        canonicalReverseChoiProjector mu nu hmu hnu hinc := by
  have hm : (canonicalReverse mu nu hmu hnu hinc).toFun =
      reverseMap
        (specifiedCartanEmbedding (canonicalWeightModel mu) (canonicalAuxiliaryModel mu nu)
          (canonicalWeightModel nu) (canonicalAuxiliaryModel_hrow mu nu hmu hnu hinc)) := by
    funext X
    rw [canonicalReverse_eq_cartan_apply mu nu hmu hnu hinc hd]
    simp only [canonicalCartanReverse, specifiedReverse, reverseChannel_apply, reverseMap]
  rw [hm]
  exact choi_reverse_eq_scaled_projector _

/-- Contracting the conjugate-flipped Choi projector gives the actual reverse channel. -/
theorem canonicalReverse_choiMap (mu nu : Fin d → ℕ)
    (hmu : Antitone mu) (hnu : Antitone nu)
    (hinc : Antitone (fun i => (nu i : ℝ) - (mu i : ℝ))) (hd : 0 < d)
    (Y : Matrix (IrrepIndex nu) (IrrepIndex nu) ℂ) :
    choiMap (((Fintype.card (IrrepIndex nu) : ℝ) / Fintype.card (IrrepIndex (auxiliaryRow mu nu))) •
      canonicalReverseChoiProjector mu nu hmu hnu hinc) Y = (canonicalReverse mu nu hmu hnu hinc).toFun Y := by
  rw [← canonicalReverse_choi mu nu hmu hnu hinc hd]
  exact choiMap_choi_linear (canonicalReverse mu nu hmu hnu hinc).toLinearMap Y

end FreeEntropy.ExteriorRepresentation
