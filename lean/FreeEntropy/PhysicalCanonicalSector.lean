/-
Copyright (c) 2026 Free Entropy formalization contributors.
See LICENSE and NOTICE in the repository root for license and attribution.
-/

import FreeEntropy.PhysicalSchurProtocol
import FreeEntropy.CanonicalClassification
import FreeEntropy.LieCharacterSymmetry

/-! The actual sector state is transported to the canonical representation
with exactly its already-proved highest occupation. This identifies the
physical source block, including normalization, without a block-form premise. -/
noncomputable section
open Matrix
open scoped BigOperators
namespace FreeEntropy.SchurWeyl
open ExteriorRepresentation
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
variable {d n : ℕ}

/-- Classification with the exact highest occupation used in the actual
concentration theorem, rather than an independently chosen partition. -/
theorem exists_sectorHighest_canonical_unitary (i : Sector d n) :
    ∃ W : Matrix (IrrepIndex (sectorHighestOccupation i).val) (SectorSpace d n i) ℂ,
      Wᴴ * W = 1 ∧ W * Wᴴ = 1 ∧ ∀ U,
        W * (physicalDecomposition d n).representation i U =
          irrepMatrix (sectorHighestOccupation i).val U * W := by
  let Q := sectorWeightUnitary i
  let v := sectorWeightHighestVector i
  have hQ : Qᴴ * Q = 1 := sectorWeightUnitary_isometry i
  have hQ' : Q * Qᴴ = 1 := sectorWeightUnitary_coisometry i
  obtain ⟨hv, hdom, hw, hr, _hc⟩ := sectorWeightHighestVector_spec i
  have hv' : Q *ᵥ v ≠ 0 := by
    intro hz
    have hh := congrArg (fun x => Qᴴ *ᵥ x) hz
    apply hv
    simpa only [Matrix.mulVec_mulVec, hQ, Matrix.one_mulVec, Matrix.mulVec_zero] using hh
  apply exists_canonical_group_unitary ((physicalDecomposition d n).representation i)
    ((physicalDecomposition d n).embedding i) ((physicalDecomposition d n).isometry i)
    ((physicalDecomposition d n).intertwines i) (sectorHighestOccupation i).val hdom
    ((tensorDegree_eq_sum _ hdom).trans (sectorHighestOccupation i).property) (Q *ᵥ v) hv'
  · intro j
    have hh := congrArg (fun x => Q *ᵥ x) (hw j)
    change Q *ᵥ ((Qᴴ * (sectorGenerators i).E j j * Q) *ᵥ v) = _ at hh
    simpa only [Matrix.mulVec_smul, Matrix.mulVec_mulVec, Matrix.mul_assoc,
      ← Matrix.mul_assoc Q Qᴴ, hQ', Matrix.one_mul] using hh
  · intro j k hjk
    have hh := congrArg (fun x => Q *ᵥ x) (hr j k hjk)
    change Q *ᵥ ((Qᴴ * (sectorGenerators i).E j k * Q) *ᵥ v) = _ at hh
    simpa only [Matrix.mulVec_zero, Matrix.mulVec_mulVec, Matrix.mul_assoc,
      ← Matrix.mul_assoc Q Qᴴ, hQ', Matrix.one_mul] using hh
  · exact sector_cyclicSpan_eq_top i (Q *ᵥ v) hv'

variable {A B : Type*} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]

/-- Equivalent physical summands have source matrices conjugated by the
actual intertwining unitary, for every Hermitian input matrix. -/
theorem source_block_unitary
    (R : Matrix.unitaryGroup (Fin d) ℂ →* Matrix A A ℂ)
    (S : Matrix.unitaryGroup (Fin d) ℂ →* Matrix B B ℂ)
    (J : Matrix (Fin n → Fin d) A ℂ) (K : Matrix (Fin n → Fin d) B ℂ)
    (hJ : Jᴴ * J = 1) (hK : Kᴴ * K = 1)
    (hJR : ∀ U, physicalRepresentation d n U * J = J * R U)
    (hKS : ∀ U, physicalRepresentation d n U * K = K * S U)
    (W : Matrix B A ℂ) (hW : Wᴴ * W = 1) (hW' : W * Wᴴ = 1)
    (hWS : ∀ U, W * R U = S U * W)
    {ρ : Matrix (Fin d) (Fin d) ℂ} (hρ : ρ.IsHermitian) :
    W * (Jᴴ * TensorPowers.matrix n ρ * J) * Wᴴ = Kᴴ * TensorPowers.matrix n ρ * K := by
  have hJW : (J * Wᴴ)ᴴ * (J * Wᴴ) = 1 := by
    simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc,
      ← Matrix.mul_assoc Jᴴ J, hJ, Matrix.one_mul, hW']
  have hWadj (U : Matrix.unitaryGroup (Fin d) ℂ) : R U * Wᴴ = Wᴴ * S U := by
    have h := congrArg (fun X => Wᴴ * X * Wᴴ) (hWS U)
    simpa only [Matrix.mul_assoc, ← Matrix.mul_assoc Wᴴ W, hW, Matrix.one_mul,
      ← Matrix.mul_assoc W Wᴴ, hW', Matrix.mul_one] using h
  have hJWS (U : Matrix.unitaryGroup (Fin d) ℂ) :
      physicalRepresentation d n U * (J * Wᴴ) = (J * Wᴴ) * S U := by
    rw [← Matrix.mul_assoc, hJR, Matrix.mul_assoc, hWadj, ← Matrix.mul_assoc]
  have h := source_blocks_equal S (J * Wᴴ) K hJW hK hJWS hKS hρ
  simpa only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc] using h

/-- Normalization commutes with an actual rectangular unitary. The zero
block case is also proved because maximally mixed states are transported. -/
theorem normalizedBlock_unitary [Nonempty A] [Nonempty B]
    (W : Matrix B A ℂ) (hW : Wᴴ * W = 1) (hW' : W * Wᴴ = 1)
    (X : Matrix A A ℂ) : normalizedBlock (W * X * Wᴴ) = W * normalizedBlock X * Wᴴ := by
  have htr : OrbitMemory.tr (W * X * Wᴴ) = OrbitMemory.tr X := by
    unfold OrbitMemory.tr
    rw [Matrix.trace_mul_cycle, hW, Matrix.one_mul]
  have hcard : Fintype.card A = Fintype.card B := by
    have h := Matrix.trace_mul_comm Wᴴ W
    rw [hW, hW', Matrix.trace_one, Matrix.trace_one] at h
    exact_mod_cast h
  unfold normalizedBlock
  rw [htr]
  split_ifs with hz
  · simp only [MultiplicityChannels.maximallyMixed, Matrix.mul_smul, Matrix.smul_mul,
      Matrix.mul_one, hW', hcard]
  · rw [Matrix.mul_smul, Matrix.smul_mul]

end FreeEntropy.SchurWeyl

namespace FreeEntropy.SchurWeyl
open ExteriorRepresentation
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
variable {d n : ℕ}
variable {A : Type*} [Fintype A] [DecidableEq A]

/-- The literal tensor source compressed into the constructed canonical irrep. -/
def canonicalTensorSource (mu : Fin d → ℕ) (ρ : Matrix (Fin d) (Fin d) ℂ) :
    Matrix (IrrepIndex mu) (IrrepIndex mu) ℂ :=
  (irrepTensorEmbedding mu)ᴴ * TensorPowers.matrix (tensorDegree mu) ρ * irrepTensorEmbedding mu

/-- The canonical normalized block is a literal physical source restriction. -/
def canonicalTensorState (mu : Fin d → ℕ) (ρ : Matrix (Fin d) (Fin d) ℂ) :
    Matrix (IrrepIndex mu) (IrrepIndex mu) ℂ := by
  letI : Nonempty (IrrepIndex mu) := Fin.pos_iff_nonempty.mp (irrep_dimension_pos mu)
  exact normalizedBlock (canonicalTensorSource mu ρ)

theorem source_block_canonical
    (R : Matrix.unitaryGroup (Fin d) ℂ →* Matrix A A ℂ)
    (J : Matrix (Fin n → Fin d) A ℂ) (hJ : Jᴴ * J = 1)
    (hJR : ∀ U, physicalRepresentation d n U * J = J * R U)
    (mu : Fin d → ℕ) (hn : tensorDegree mu = n)
    (W : Matrix (IrrepIndex mu) A ℂ) (hW : Wᴴ * W = 1) (hW' : W * Wᴴ = 1)
    (hWS : ∀ U, W * R U = irrepMatrix mu U * W)
    {ρ : Matrix (Fin d) (Fin d) ℂ} (hρ : ρ.IsHermitian) :
    W * (Jᴴ * TensorPowers.matrix n ρ * J) * Wᴴ = canonicalTensorSource mu ρ := by
  subst n
  exact source_block_unitary R (irrepMatrix mu) J (irrepTensorEmbedding mu) hJ
    (irrepTensorEmbedding_isometry mu) hJR (irrepTensorEmbedding_intertwines mu) W hW hW' hWS hρ

/-- The actual unitary identifying a sector with its exact highest-weight canonical model. -/
def sectorCanonicalUnitary (i : Sector d n) :
    Matrix (IrrepIndex (sectorHighestOccupation i).val) (SectorSpace d n i) ℂ :=
  (exists_sectorHighest_canonical_unitary i).choose

theorem sectorCanonicalUnitary_spec (i : Sector d n) :
    (sectorCanonicalUnitary i)ᴴ * sectorCanonicalUnitary i = 1 ∧
      sectorCanonicalUnitary i * (sectorCanonicalUnitary i)ᴴ = 1 ∧ ∀ U,
      sectorCanonicalUnitary i * (physicalDecomposition d n).representation i U =
        irrepMatrix (sectorHighestOccupation i).val U * sectorCanonicalUnitary i :=
  (exists_sectorHighest_canonical_unitary i).choose_spec

/-- Exact source identification under the actual classification unitary. -/
theorem physicalBlock_canonical (i : Sector d n) {ρ : Matrix (Fin d) (Fin d) ℂ}
    (hρ : ρ.IsHermitian) :
    sectorCanonicalUnitary i * physicalBlock n ρ i * (sectorCanonicalUnitary i)ᴴ =
      canonicalTensorSource (sectorHighestOccupation i).val ρ := by
  obtain ⟨hW, hW', hWS⟩ := sectorCanonicalUnitary_spec i
  exact source_block_canonical ((physicalDecomposition d n).representation i)
    ((physicalDecomposition d n).embedding i) ((physicalDecomposition d n).isometry i)
    ((physicalDecomposition d n).intertwines i) (sectorHighestOccupation i).val
    ((tensorDegree_eq_sum _ (sectorWeightHighestVector_spec i).2.1).trans
      (sectorHighestOccupation i).property) (sectorCanonicalUnitary i) hW hW' hWS hρ

/-- Normalized physical sector states are the canonical physical states,
including the case of zero sector probability. -/
theorem sectorState_canonical (i : Sector d n) {ρ : Matrix (Fin d) (Fin d) ℂ}
    (hρ : ρ.IsHermitian) :
    sectorCanonicalUnitary i * sectorState n ρ i * (sectorCanonicalUnitary i)ᴴ =
      canonicalTensorState (sectorHighestOccupation i).val ρ := by
  letI : Nonempty (IrrepIndex (sectorHighestOccupation i).val) :=
    Fin.pos_iff_nonempty.mp (irrep_dimension_pos _)
  obtain ⟨hW, hW', _⟩ := sectorCanonicalUnitary_spec i
  change sectorCanonicalUnitary i * normalizedBlock (physicalBlock n ρ i) *
    (sectorCanonicalUnitary i)ᴴ = normalizedBlock (canonicalTensorSource _ ρ)
  rw [← normalizedBlock_unitary _ hW hW', physicalBlock_canonical i hρ]

theorem canonicalTensorSource_weight_diagonal (mu : Fin d → ℕ) (z : Fin d → ℂ) :
    (canonicalWeightCoordinates mu).unitaryᴴ * canonicalTensorSource mu (Matrix.diagonal z) *
      (canonicalWeightCoordinates mu).unitary =
        Matrix.diagonal (fun a => ∏ j, z j ^ canonicalWeight mu a j) := by
  have h := LieCharacter.physical_weight_source (canonicalPhysicalWeightEmbedding mu)
    (canonicalWeight mu) (canonicalPhysicalWeightEmbedding_diagonal mu) z
  have hh := congrArg (fun X => (canonicalPhysicalWeightEmbedding mu)ᴴ * X) h
  dsimp only at hh
  rw [← Matrix.mul_assoc (canonicalPhysicalWeightEmbedding mu)ᴴ
    (canonicalPhysicalWeightEmbedding mu), canonicalPhysicalWeightEmbedding_isometry, Matrix.one_mul] at hh
  simpa only [canonicalPhysicalWeightEmbedding, canonicalTensorSource,
    Matrix.conjTranspose_mul, Matrix.mul_assoc] using hh

/-- Literal normalized occupation monomials in the canonical weight basis. -/
def canonicalMonomialState (mu : Fin d → ℕ) (z : Fin d → ℂ) :
    Matrix (IrrepIndex mu) (IrrepIndex mu) ℂ := by
  letI : Nonempty (IrrepIndex mu) := Fin.pos_iff_nonempty.mp (irrep_dimension_pos mu)
  exact normalizedBlock (Matrix.diagonal (fun a => ∏ j, z j ^ canonicalWeight mu a j))

/-- The exact normalized canonical weight-basis source is the normalized
monomial diagonal, including rank-deficient physical spectra. -/
theorem canonicalTensorState_weight_diagonal (mu : Fin d → ℕ) (z : Fin d → ℂ) :
    (canonicalWeightCoordinates mu).unitaryᴴ * canonicalTensorState mu (Matrix.diagonal z) *
      (canonicalWeightCoordinates mu).unitary =
        canonicalMonomialState mu z := by
  letI : Nonempty (IrrepIndex mu) := Fin.pos_iff_nonempty.mp (irrep_dimension_pos mu)
  change (canonicalWeightCoordinates mu).unitaryᴴ * normalizedBlock _ *
    (canonicalWeightCoordinates mu).unitary = normalizedBlock _
  have hW := (canonicalWeightCoordinates mu).isometry
  have hW' := mul_eq_one_comm.mp hW
  have hh := normalizedBlock_unitary (canonicalWeightCoordinates mu).unitaryᴴ
    (by simpa using hW') (by simpa using hW) (canonicalTensorSource mu (Matrix.diagonal z))
  simpa only [Matrix.conjTranspose_conjTranspose, canonicalTensorSource_weight_diagonal] using hh.symm

end FreeEntropy.SchurWeyl
