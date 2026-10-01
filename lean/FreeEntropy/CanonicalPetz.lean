/-
Copyright (c) 2026 Free Entropy formalization contributors.
See LICENSE and NOTICE in the repository root for license and attribution.
-/

import FreeEntropy.CanonicalCloningSelf
import FreeEntropy.MultiplicityChannels

/-! The actual canonical reverse cloner is the Petz recovery map of the
forward cloner at its maximally mixed input. The adjoint is characterized
by the Hilbert--Schmidt pairing, and the recovery expression uses the
literal matrix square root and inverse, not an assumed recovery identity. -/
noncomputable section
open Matrix
open scoped BigOperators MatrixOrder ComplexOrder
namespace FreeEntropy.Petz
open Channels MultiplicityChannels
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
variable {A B : Type*} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]

/-- The usual finite-dimensional Petz expression, with the supplied adjoint
and with matrix inverses on the faithful output reference state. -/
def recovery (F : MatrixChannel A B)
    (adjoint : Matrix B B ℂ →ₗ[ℂ] Matrix A A ℂ)
    (sigma : Matrix A A ℂ) (Y : Matrix B B ℂ) : Matrix A A ℂ :=
  CFC.sqrt sigma * adjoint ((CFC.sqrt (F.toFun sigma))⁻¹ * Y *
    (CFC.sqrt (F.toFun sigma))⁻¹) * CFC.sqrt sigma

theorem sqrt_scalar_one (x : ℝ) (hx : 0 ≤ x) :
    CFC.sqrt (x • (1 : Matrix A A ℂ)) = Real.sqrt x • (1 : Matrix A A ℂ) := by
  apply (CFC.sqrt_eq_iff _ _ (Matrix.PosSemidef.one.smul hx).nonneg
    (Matrix.PosSemidef.one.smul (Real.sqrt_nonneg x)).nonneg).mpr
  rw [Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, smul_smul, Real.mul_self_sqrt hx]

theorem inv_scalar_one (x : ℝ) (hx : x ≠ 0) :
    (x • (1 : Matrix A A ℂ))⁻¹ = x⁻¹ • (1 : Matrix A A ℂ) := by
  apply Matrix.inv_eq_left_inv
  rw [Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, smul_smul, inv_mul_cancel₀ hx, one_smul]

theorem sqrt_maximallyMixed :
    CFC.sqrt (maximallyMixed A) = (Real.sqrt (Fintype.card A : ℝ))⁻¹ • (1 : Matrix A A ℂ) := by
  rw [maximallyMixed, sqrt_scalar_one _ (inv_nonneg.mpr (Nat.cast_nonneg _)), Real.sqrt_inv]

theorem inv_sqrt_maximallyMixed [Nonempty A] :
    (CFC.sqrt (maximallyMixed A))⁻¹ = Real.sqrt (Fintype.card A : ℝ) • (1 : Matrix A A ℂ) := by
  rw [sqrt_maximallyMixed, inv_scalar_one, inv_inv]
  exact inv_ne_zero (Real.sqrt_ne_zero'.mpr (by exact_mod_cast Fintype.card_pos))

/-- At maximally mixed input and output references, the literal Petz
formula simplifies to the dimension-normalized adjoint. -/
theorem recovery_maximallyMixed [Nonempty A] [Nonempty B]
    (F : MatrixChannel A B) (adjoint : Matrix B B ℂ →ₗ[ℂ] Matrix A A ℂ)
    (hF : F.toFun (maximallyMixed A) = maximallyMixed B) (Y : Matrix B B ℂ) :
    recovery F adjoint (maximallyMixed A) Y =
      ((Fintype.card B : ℝ) / (Fintype.card A : ℝ)) • adjoint Y := by
  rw [recovery, hF, sqrt_maximallyMixed, inv_sqrt_maximallyMixed]
  simp only [Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one, smul_smul,
    LinearMap.map_smul_of_tower]
  rw [Real.mul_self_sqrt (Nat.cast_nonneg _)]
  congr 1
  calc
    _ = (Fintype.card B : ℝ) * (Real.sqrt (Fintype.card A : ℝ) *
        Real.sqrt (Fintype.card A : ℝ))⁻¹ := by rw [_root_.mul_inv_rev]; ring
    _ = _ := by rw [Real.mul_self_sqrt (Nat.cast_nonneg _)]; rfl

end FreeEntropy.Petz

namespace FreeEntropy.ExteriorRepresentation
open Channels CartanLieCloning CartanChannel MultiplicityChannels
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
variable {d : ℕ}
local instance (mu : Fin d → ℕ) : Nonempty (IrrepIndex mu) :=
  Fin.pos_iff_nonempty.mp (irrep_dimension_pos mu)

/-- A concrete complex-linear candidate for the Hilbert--Schmidt adjoint.
Its defining pairing with the actual forward map is proved below. -/
def canonicalAdjoint (mu nu : Fin d → ℕ) (hmu : Antitone mu) (hnu : Antitone nu)
    (hinc : Antitone (fun i => (nu i : ℝ) - (mu i : ℝ))) :
    Matrix (IrrepIndex nu) (IrrepIndex nu) ℂ →ₗ[ℂ] Matrix (IrrepIndex mu) (IrrepIndex mu) ℂ :=
  ((Fintype.card (IrrepIndex mu) : ℝ) / (Fintype.card (IrrepIndex nu) : ℝ)) •
    (canonicalReverse mu nu hmu hnu hinc).toLinearMap

theorem canonicalAdjoint_eq_sectorAdjoint (mu nu : Fin d → ℕ)
    (hmu : Antitone mu) (hnu : Antitone nu)
    (hinc : Antitone (fun i => (nu i : ℝ) - (mu i : ℝ))) (hd : 0 < d)
    (Y : Matrix (IrrepIndex nu) (IrrepIndex nu) ℂ) :
    canonicalAdjoint mu nu hmu hnu hinc Y =
      sectorAdjoint (Fintype.card (IrrepIndex mu)) (Fintype.card (IrrepIndex nu))
        (specifiedCartanEmbedding (canonicalWeightModel mu) (canonicalAuxiliaryModel mu nu)
          (canonicalWeightModel nu) (canonicalAuxiliaryModel_hrow mu nu hmu hnu hinc)) Y := by
  change ((Fintype.card (IrrepIndex mu) : ℝ) / (Fintype.card (IrrepIndex nu) : ℝ)) •
    (canonicalReverse mu nu hmu hnu hinc).toFun Y = _
  rw [canonicalReverse_eq_cartan_apply mu nu hmu hnu hinc hd Y]
  simp only [canonicalCartanReverse, specifiedReverse, reverseChannel_apply, sectorAdjoint, reverseMap]

/-- The literal Hilbert--Schmidt pairing identifies the actual adjoint. -/
theorem canonicalAdjoint_hilbertSchmidt (mu nu : Fin d → ℕ)
    (hmu : Antitone mu) (hnu : Antitone nu)
    (hinc : Antitone (fun i => (nu i : ℝ) - (mu i : ℝ))) (hd : 0 < d)
    (X : Matrix (IrrepIndex mu) (IrrepIndex mu) ℂ)
    (Y : Matrix (IrrepIndex nu) (IrrepIndex nu) ℂ) :
    (((canonicalForward mu nu hmu hnu hinc).toFun X)ᴴ * Y).trace =
      (Xᴴ * canonicalAdjoint mu nu hmu hnu hinc Y).trace := by
  rw [canonicalForward_eq_cartan_apply mu nu hmu hnu hinc hd X,
    canonicalAdjoint_eq_sectorAdjoint mu nu hmu hnu hinc hd Y]
  simp only [canonicalCartanForward, specifiedForward, cartanChannel_apply]
  exact sectorMap_hilbertSchmidt_pairing _ _ _ X Y

/-- Nondegeneracy of the matrix trace pairing makes the proved
Hilbert--Schmidt adjoint unique. -/
theorem canonicalAdjoint_unique (mu nu : Fin d → ℕ)
    (hmu : Antitone mu) (hnu : Antitone nu)
    (hinc : Antitone (fun i => (nu i : ℝ) - (mu i : ℝ))) (hd : 0 < d)
    (T : Matrix (IrrepIndex nu) (IrrepIndex nu) ℂ →ₗ[ℂ]
      Matrix (IrrepIndex mu) (IrrepIndex mu) ℂ)
    (hT : ∀ X Y, (((canonicalForward mu nu hmu hnu hinc).toFun X)ᴴ * Y).trace =
      (Xᴴ * T Y).trace) : T = canonicalAdjoint mu nu hmu hnu hinc := by
  apply LinearMap.ext
  intro Y
  apply Matrix.ext_iff_trace_mul_left.mpr
  intro X
  have h := (hT Xᴴ Y).symm.trans (canonicalAdjoint_hilbertSchmidt mu nu hmu hnu hinc hd Xᴴ Y)
  simpa only [Matrix.conjTranspose_conjTranspose] using h

/-- The adjoint relation in the reverse-cloner proposition, as an exact
identity of matrices for every input. -/
theorem canonicalReverse_eq_normalized_adjoint (mu nu : Fin d → ℕ)
    (hmu : Antitone mu) (hnu : Antitone nu)
    (hinc : Antitone (fun i => (nu i : ℝ) - (mu i : ℝ)))
    (Y : Matrix (IrrepIndex nu) (IrrepIndex nu) ℂ) :
    (canonicalReverse mu nu hmu hnu hinc).toFun Y =
      ((Fintype.card (IrrepIndex nu) : ℝ) / (Fintype.card (IrrepIndex mu) : ℝ)) •
        canonicalAdjoint mu nu hmu hnu hinc Y := by
  change (canonicalReverse mu nu hmu hnu hinc).toFun Y =
    ((Fintype.card (IrrepIndex nu) : ℝ) / (Fintype.card (IrrepIndex mu) : ℝ)) •
      (((Fintype.card (IrrepIndex mu) : ℝ) / (Fintype.card (IrrepIndex nu) : ℝ)) •
        (canonicalReverse mu nu hmu hnu hinc).toFun Y)
  rw [smul_smul]
  have hmu0 : (Fintype.card (IrrepIndex mu) : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hnu0 : (Fintype.card (IrrepIndex nu) : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hc : (Fintype.card (IrrepIndex nu) : ℝ) / (Fintype.card (IrrepIndex mu) : ℝ) *
      ((Fintype.card (IrrepIndex mu) : ℝ) / (Fintype.card (IrrepIndex nu) : ℝ)) = 1 := by field_simp
  rw [hc, one_smul]

/-- The reference output is exactly the maximally mixed target state. -/
theorem canonicalForward_maximallyMixed (mu nu : Fin d → ℕ)
    (hmu : Antitone mu) (hnu : Antitone nu)
    (hinc : Antitone (fun i => (nu i : ℝ) - (mu i : ℝ))) (hd : 0 < d) :
    (canonicalForward mu nu hmu hnu hinc).toFun (maximallyMixed (IrrepIndex mu)) =
      maximallyMixed (IrrepIndex nu) := by
  rw [canonicalForward_eq_cartan_apply mu nu hmu hnu hinc hd]
  simp only [canonicalCartanForward, specifiedForward, cartanChannel_apply, maximallyMixed]
  simpa only [one_div] using sectorMap_maximally_mixed
    (specifiedCartanEmbedding (canonicalWeightModel mu) (canonicalAuxiliaryModel mu nu)
      (canonicalWeightModel nu) (canonicalAuxiliaryModel_hrow mu nu hmu hnu hinc))
    (Fintype.card (IrrepIndex mu)) (Fintype.card (IrrepIndex nu))
    (by exact_mod_cast Fintype.card_ne_zero)
    (specifiedCartanEmbedding_isometry _ _ _ _)

/-- The literal Petz recovery expression equals the actual reverse CPTP
cloner, for every matrix, including the zero-difference case. -/
theorem canonicalPetz_eq_reverse (mu nu : Fin d → ℕ)
    (hmu : Antitone mu) (hnu : Antitone nu)
    (hinc : Antitone (fun i => (nu i : ℝ) - (mu i : ℝ))) (hd : 0 < d)
    (Y : Matrix (IrrepIndex nu) (IrrepIndex nu) ℂ) :
    Petz.recovery (canonicalForward mu nu hmu hnu hinc) (canonicalAdjoint mu nu hmu hnu hinc)
      (maximallyMixed (IrrepIndex mu)) Y = (canonicalReverse mu nu hmu hnu hinc).toFun Y := by
  rw [Petz.recovery_maximallyMixed _ _ (canonicalForward_maximallyMixed mu nu hmu hnu hinc hd)]
  exact (canonicalReverse_eq_normalized_adjoint mu nu hmu hnu hinc Y).symm

end FreeEntropy.ExteriorRepresentation
