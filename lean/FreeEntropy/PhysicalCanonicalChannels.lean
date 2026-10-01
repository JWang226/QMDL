/-
Copyright (c) 2026 Free Entropy formalization contributors.
See LICENSE and NOTICE in the repository root for license and attribution.
-/

import FreeEntropy.PhysicalCanonicalSector

/-! Canonical cloning maps are transported to actual physical sectors by
constructed classification unitaries. Both state and error identifications
are proved, so they can be plugged into the literal physical protocol. -/
noncomputable section
open Matrix
open scoped MatrixOrder ComplexOrder
namespace FreeEntropy.SchurWeyl
open Channels TraceDistance ExteriorRepresentation
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
variable {d n r : ℕ} {M : Type*} [Fintype M] [DecidableEq M]

theorem canonicalTensorState_positive (mu : Fin d → ℕ) {ρ : Matrix (Fin d) (Fin d) ℂ}
    (hρ : ρ.PosSemidef) : (canonicalTensorState mu ρ).PosSemidef := by
  letI : Nonempty (IrrepIndex mu) := Fin.pos_iff_nonempty.mp (irrep_dimension_pos mu)
  exact normalizedBlock_positive (source_compressed_positive (irrepTensorEmbedding mu) hρ)

theorem canonicalTensorState_trace (mu : Fin d → ℕ) {ρ : Matrix (Fin d) (Fin d) ℂ}
    (hρ : ρ.PosSemidef) : (canonicalTensorState mu ρ).trace = 1 := by
  letI : Nonempty (IrrepIndex mu) := Fin.pos_iff_nonempty.mp (irrep_dimension_pos mu)
  exact normalizedBlock_trace (source_compressed_positive (irrepTensorEmbedding mu) hρ)

theorem sectorState_canonical_pullback (i : Sector d n) {ρ : Matrix (Fin d) (Fin d) ℂ}
    (hρ : ρ.IsHermitian) : sectorState n ρ i =
      (sectorCanonicalUnitary i)ᴴ * canonicalTensorState (sectorHighestOccupation i).val ρ *
        sectorCanonicalUnitary i := by
  rw [← sectorState_canonical i hρ]
  have hW := (sectorCanonicalUnitary_spec i).1
  simp only [Matrix.mul_assoc, ← Matrix.mul_assoc (sectorCanonicalUnitary i)ᴴ
    (sectorCanonicalUnitary i), hW, Matrix.one_mul, Matrix.mul_one]

/-- Forward cloning on a physical sector, after the actual canonical unitary. -/
def sectorCanonicalForward (i : Sector d n)
    (F : MatrixChannel (IrrepIndex (sectorHighestOccupation i).val) M) :
    MatrixChannel (SectorSpace d n i) M :=
  F.comp (SchurProtocol.changeBasisChannel (sectorCanonicalUnitary i) (sectorCanonicalUnitary_spec i).1)

/-- Reverse cloning followed by the inverse actual classification unitary. -/
def sectorCanonicalReverse (i : Sector d n)
    (G : MatrixChannel M (IrrepIndex (sectorHighestOccupation i).val)) :
    MatrixChannel M (SectorSpace d n i) :=
  (SchurProtocol.changeBasisChannel (sectorCanonicalUnitary i)ᴴ
    (by simpa using (sectorCanonicalUnitary_spec i).2.1)).comp G

theorem sectorCanonicalForward_state (i : Sector d n)
    (F : MatrixChannel (IrrepIndex (sectorHighestOccupation i).val) M)
    {ρ : Matrix (Fin d) (Fin d) ℂ} (hρ : ρ.IsHermitian) :
    (sectorCanonicalForward i F).toFun (sectorState n ρ i) =
      F.toFun (canonicalTensorState (sectorHighestOccupation i).val ρ) := by
  change F.toFun ((SchurProtocol.changeBasisChannel _ _).toFun _) = _
  rw [SchurProtocol.changeBasisChannel_apply, sectorState_canonical i hρ]

/-- Reverse trace error is exactly the canonical reverse error. -/
theorem sectorCanonicalReverse_error (i : Sector d n)
    (G : MatrixChannel M (IrrepIndex (sectorHighestOccupation i).val))
    {ρ : Matrix (Fin d) (Fin d) ℂ} (hρ : ρ.PosSemidef)
    {τ : Matrix M M ℂ} (hτ : τ.PosSemidef) :
    traceDistance ((sectorCanonicalReverse i G).toFun τ) (sectorState n ρ i) =
      traceDistance (G.toFun τ) (canonicalTensorState (sectorHighestOccupation i).val ρ) := by
  simp only [sectorCanonicalReverse, MatrixChannel.comp]
  rw [SchurProtocol.changeBasisChannel_apply, sectorState_canonical_pullback i hρ.isHermitian]
  have h := traceDistance_isometry (sectorCanonicalUnitary i)ᴴ
    (by simpa using (sectorCanonicalUnitary_spec i).2.1) (G.positive _ hτ)
    (canonicalTensorState_positive _ hρ)
  simpa only [Matrix.conjTranspose_conjTranspose] using h

/-- Actual tensor-source compression from canonical local cloning bounds.
All source decomposition, classification, normalization and tail inputs
have been replaced by proved concrete constructions. -/
theorem physical_roundtrip_from_canonical (s : FixedSpectrum d r) (n : ℕ) (hn : 2 ≤ n)
    (F : ∀ i : Sector d n, MatrixChannel (IrrepIndex (sectorHighestOccupation i).val) M)
    (G : ∀ i : Sector d n, MatrixChannel M (IrrepIndex (sectorHighestOccupation i).val))
    (U : Matrix.unitaryGroup (Fin d) ℂ) (τ : Matrix M M ℂ)
    (hτ : τ.PosSemidef) (hτ1 : τ.trace = 1) (ε : ℝ) (hε : 0 ≤ ε)
    (hf : ∀ i ∈ physicalTypical s n,
      traceDistance ((F i).toFun (canonicalTensorState (sectorHighestOccupation i).val
        (physicalDensity s U))) τ ≤ ε)
    (hr : ∀ i ∈ physicalTypical s n,
      traceDistance ((G i).toFun τ) (canonicalTensorState (sectorHighestOccupation i).val
        (physicalDensity s U)) ≤ ε) :
    traceDistance ((physicalDecoder s n (fun i => sectorCanonicalReverse i (G i))).toFun
      ((physicalEncoder (fun i => sectorCanonicalForward i (F i))).toFun
        (TensorPowers.matrix n (physicalDensity s U))))
      (TensorPowers.matrix n (physicalDensity s U)) ≤
        2 * ε + 2 * Concentration.tailBound (concentrationExponent d + d) n := by
  apply physical_roundtrip_error_le s n hn _ _ U τ hτ hτ1 ε hε
  · intro i hi
    change traceDistance ((sectorCanonicalForward i (F i)).toFun
      (sectorState n (physicalDensity s U) i)) τ ≤ ε
    rw [sectorCanonicalForward_state i (F i) (physicalDensity_positive s U).isHermitian]
    exact hf i hi
  · intro i hi
    change traceDistance ((sectorCanonicalReverse i (G i)).toFun τ)
      (sectorState n (physicalDensity s U) i) ≤ ε
    rw [sectorCanonicalReverse_error i (G i) (physicalDensity_positive s U) hτ]
    exact hr i hi

end FreeEntropy.SchurWeyl
