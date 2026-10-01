/-
Copyright (c) 2026 Free Entropy formalization contributors.
See LICENSE and NOTICE in the repository root for license and attribution.
-/

import FreeEntropy.SchurWeylSource
import FreeEntropy.Twirling

/-!
# Actual mixed tensor-power blocks from unitary intertwiners

An isometric unitary intertwiner automatically reduces the physical source.
Orthogonal summands have zero source cross-blocks, and two copies of the same
representation have identical source matrices. Thus the source block identity
is derived from genuine representation intertwiners, never assumed.
-/
noncomputable section
open scoped BigOperators ComplexOrder MatrixOrder
open Matrix
namespace FreeEntropy.SchurWeyl
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
set_option linter.unusedSectionVars false
variable {d n : ℕ}
variable {A B : Type*} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]

/-- The actual tensor-power representation of the physical unitary group. -/
def physicalRepresentation (d n : ℕ) : Matrix.unitaryGroup (Fin d) ℂ →*
    Matrix (Fin n → Fin d) (Fin n → Fin d) ℂ :=
  TensorPowers.representation n (Matrix.unitaryGroup (Fin d) ℂ).subtype

theorem physicalRepresentation_unitary (d n : ℕ) (U : Matrix.unitaryGroup (Fin d) ℂ) :
    (physicalRepresentation d n U)ᴴ * physicalRepresentation d n U = 1 :=
  TensorPowers.matrix_unitary n (Matrix.UnitaryGroup.star_mul_self U)

/-- A genuinely isometric restriction of the physical action is automatically unitary. -/
theorem restriction_unitary
    (R : Matrix.unitaryGroup (Fin d) ℂ →* Matrix A A ℂ)
    (J : Matrix (Fin n → Fin d) A ℂ) (hJ : Jᴴ * J = 1)
    (hJR : ∀ U, physicalRepresentation d n U * J = J * R U)
    (U : Matrix.unitaryGroup (Fin d) ℂ) : (R U)ᴴ * R U = 1 := by
  calc
    _ = (R U)ᴴ * (Jᴴ * J) * R U := by rw [hJ]; simp
    _ = (J * R U)ᴴ * (J * R U) := by
      rw [Matrix.conjTranspose_mul]
      simp only [Matrix.mul_assoc]
    _ = (physicalRepresentation d n U * J)ᴴ * (physicalRepresentation d n U * J) := by
      rw [hJR U]
    _ = Jᴴ * ((physicalRepresentation d n U)ᴴ * physicalRepresentation d n U) * J := by
      rw [Matrix.conjTranspose_mul]
      simp only [Matrix.mul_assoc]
    _ = 1 := by rw [physicalRepresentation_unitary, Matrix.mul_one, hJ]

/-- The adjoint of an isometric intertwiner intertwines in the reverse direction. -/
theorem intertwiner_adjoint
    (R : Matrix.unitaryGroup (Fin d) ℂ →* Matrix A A ℂ)
    (J : Matrix (Fin n → Fin d) A ℂ) (hJ : Jᴴ * J = 1)
    (hJR : ∀ U, physicalRepresentation d n U * J = J * R U)
    (U : Matrix.unitaryGroup (Fin d) ℂ) :
    Jᴴ * physicalRepresentation d n U = R U * Jᴴ := by
  have h := congrArg Matrix.conjTranspose (hJR U⁻¹)
  rw [Twirling.inverse_eq_conjTranspose (physicalRepresentation d n)
    (physicalRepresentation_unitary d n),
    Twirling.inverse_eq_conjTranspose R (restriction_unitary R J hJ hJR)] at h
  simpa only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose] using h

/-- Matrix units between equivalent representation copies are genuine
operators in the physical tensor-unitary commutant. -/
theorem copy_matrixUnit_commutant
    (R : Matrix.unitaryGroup (Fin d) ℂ →* Matrix A A ℂ)
    (J K : Matrix (Fin n → Fin d) A ℂ) (hK : Kᴴ * K = 1)
    (hJR : ∀ U, physicalRepresentation d n U * J = J * R U)
    (hKR : ∀ U, physicalRepresentation d n U * K = K * R U) :
    TensorCommutant (J * Kᴴ) := by
  intro U
  change J * Kᴴ * physicalRepresentation d n U = physicalRepresentation d n U * (J * Kᴴ)
  rw [Matrix.mul_assoc, intertwiner_adjoint R K hK hKR, ← Matrix.mul_assoc,
    ← hJR U, Matrix.mul_assoc]

/-- The mixed tensor-power source preserves every genuine isometric summand. -/
theorem source_intertwines
    (R : Matrix.unitaryGroup (Fin d) ℂ →* Matrix A A ℂ)
    (J : Matrix (Fin n → Fin d) A ℂ) (hJ : Jᴴ * J = 1)
    (hJR : ∀ U, physicalRepresentation d n U * J = J * R U)
    {ρ : Matrix (Fin d) (Fin d) ℂ} (hρ : ρ.IsHermitian) :
    TensorPowers.matrix n ρ * J = J * (Jᴴ * TensorPowers.matrix n ρ * J) := by
  have h := (copy_matrixUnit_commutant R J J hJ hJR hJR).hermitian hρ
  have he := congrArg (fun X => X * J) h
  simpa only [Matrix.mul_assoc, hJ, Matrix.mul_one] using he.symm

/-- Orthogonal representation copies have exactly zero cross-blocks in
the actual physical tensor-power source. -/
theorem source_crossBlock_zero
    (R : Matrix.unitaryGroup (Fin d) ℂ →* Matrix B B ℂ)
    (J : Matrix (Fin n → Fin d) A ℂ) (K : Matrix (Fin n → Fin d) B ℂ)
    (hK : Kᴴ * K = 1) (hJK : Jᴴ * K = 0)
    (hKR : ∀ U, physicalRepresentation d n U * K = K * R U)
    {ρ : Matrix (Fin d) (Fin d) ℂ} (hρ : ρ.IsHermitian) :
    Jᴴ * TensorPowers.matrix n ρ * K = 0 := by
  rw [Matrix.mul_assoc, source_intertwines R K hK hKR hρ,
    ← Matrix.mul_assoc, hJK, Matrix.zero_mul]

/-- Equivalent copies have literally identical unnormalized source blocks.
This is the source of the identity on every multiplicity register. -/
theorem source_blocks_equal
    (R : Matrix.unitaryGroup (Fin d) ℂ →* Matrix A A ℂ)
    (J K : Matrix (Fin n → Fin d) A ℂ) (hJ : Jᴴ * J = 1) (hK : Kᴴ * K = 1)
    (hJR : ∀ U, physicalRepresentation d n U * J = J * R U)
    (hKR : ∀ U, physicalRepresentation d n U * K = K * R U)
    {ρ : Matrix (Fin d) (Fin d) ℂ} (hρ : ρ.IsHermitian) :
    Jᴴ * TensorPowers.matrix n ρ * J = Kᴴ * TensorPowers.matrix n ρ * K := by
  have h := (copy_matrixUnit_commutant R J K hK hJR hKR).hermitian hρ
  have he := congrArg (fun X => Jᴴ * X * K) h
  have hl : Jᴴ * (J * Kᴴ * TensorPowers.matrix n ρ) * K =
      Kᴴ * TensorPowers.matrix n ρ * K := by
    simp only [← Matrix.mul_assoc, hJ, Matrix.one_mul]
  have hr : Jᴴ * (TensorPowers.matrix n ρ * (J * Kᴴ)) * K =
      Jᴴ * TensorPowers.matrix n ρ * J := by
    simp only [Matrix.mul_assoc, hK, Matrix.mul_one]
  dsimp only at he
  rw [hl, hr] at he
  exact he.symm

/-- A complete orthogonal unitary decomposition gives the exact mixed-state
block decomposition. Only representation data enter; the source formula is
a conclusion for every Hermitian physical matrix. -/
theorem source_block_sum {ι : Type*} [Fintype ι]
    {D : ι → Type*} [∀ i, Fintype (D i)] [∀ i, DecidableEq (D i)]
    (R : ∀ i, Matrix.unitaryGroup (Fin d) ℂ →* Matrix (D i) (D i) ℂ)
    (J : ∀ i, Matrix (Fin n → Fin d) (D i) ℂ)
    (hJ : ∀ i, (J i)ᴴ * J i = 1)
    (hJR : ∀ i U, physicalRepresentation d n U * J i = J i * R i U)
    (hfull : ∑ i, J i * (J i)ᴴ = 1)
    {ρ : Matrix (Fin d) (Fin d) ℂ} (hρ : ρ.IsHermitian) :
    TensorPowers.matrix n ρ = ∑ i, J i * ((J i)ᴴ * TensorPowers.matrix n ρ * J i) * (J i)ᴴ := by
  calc
    _ = TensorPowers.matrix n ρ * (∑ i, J i * (J i)ᴴ) := by rw [hfull, Matrix.mul_one]
    _ = ∑ i, (TensorPowers.matrix n ρ * J i) * (J i)ᴴ := by
      rw [Matrix.mul_sum]
      simp only [Matrix.mul_assoc]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i _
      rw [source_intertwines (R i) (J i) (hJ i) (hJR i) hρ]

end FreeEntropy.SchurWeyl
