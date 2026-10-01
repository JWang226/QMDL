/-
Copyright (c) 2026 Free Entropy formalization contributors.
See LICENSE and NOTICE in the repository root for license and attribution.
-/

import FreeEntropy.CanonicalPhysicalOrbit
import FreeEntropy.CanonicalMonomialState
import FreeEntropy.PhysicalSchurApproximation

/-! Actual physical-source channels assembled from canonical weight-orbit
cloning maps. The physical source, its typical sectors, and the canonical
orbit states are identified by proved constructions, including zero spectra. -/
noncomputable section
open Matrix
open scoped MatrixOrder ComplexOrder
namespace FreeEntropy.SchurWeyl
open Channels TraceDistance ExteriorRepresentation
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
set_option linter.unusedSectionVars false
variable {d r n : ℕ} {M : Type*} [Fintype M] [DecidableEq M]

theorem canonicalWeightTensorState_eq_orbit (s : FixedSpectrum d r) (mu : Fin d → ℕ)
    (hmu : Antitone mu) (hsupp : ∀ j, r ≤ j.val → mu j = 0)
    (U : Matrix.unitaryGroup (Fin d) ℂ) :
    canonicalWeightTensorState mu (physicalDensity s U) = canonicalOrbitState s mu U := by
  rw [physicalDensity, canonicalWeightTensorState_diagonal_orbit]
  change canonicalWeightRepresentation mu U *
    canonicalMonomialState mu (fun j => (s.eigenvalue j.val : ℂ)) *
      (canonicalWeightRepresentation mu U)ᴴ = _
  rw [canonicalMonomialState_eq_relativeState s mu hmu hsupp]
  rfl

theorem physicalTypical_highest_supported (s : FixedSpectrum d r) (n : ℕ) (i : Sector d n)
    (hi : i ∈ physicalTypical s n) : ∀ j : Fin d, r ≤ j.val → (sectorHighestOccupation i).val j = 0 := by
  classical
  have ht := (Finset.mem_filter.mp hi).2
  intro j hj
  have h := ht.2 j.val hj j.isLt
  simp only [occupationRow, dif_pos j.isLt] at h
  exact_mod_cast h

/-- The actual normalized physical sector becomes exactly the canonical
weight orbit, on every sector in the actual supported typical window. -/
theorem physicalSectorState_canonicalOrbit (s : FixedSpectrum d r) (n : ℕ)
    (U : Matrix.unitaryGroup (Fin d) ℂ) (i : Sector d n) (hi : i ∈ physicalTypical s n) :
    sectorWeightCanonicalUnitary i * physicalSectorState s n U i * (sectorWeightCanonicalUnitary i)ᴴ =
      canonicalOrbitState s (sectorHighestOccupation i).val U := by
  rw [physicalSectorState, sectorState_canonicalWeight i (physicalDensity_positive s U).isHermitian,
    canonicalWeightTensorState_eq_orbit s _ (sectorWeightHighestVector_spec i).2.1
      (physicalTypical_highest_supported s n i hi)]

theorem physicalSectorState_canonicalOrbit_pullback (s : FixedSpectrum d r) (n : ℕ)
    (U : Matrix.unitaryGroup (Fin d) ℂ) (i : Sector d n) (hi : i ∈ physicalTypical s n) :
    physicalSectorState s n U i = (sectorWeightCanonicalUnitary i)ᴴ *
      canonicalOrbitState s (sectorHighestOccupation i).val U * sectorWeightCanonicalUnitary i := by
  rw [← physicalSectorState_canonicalOrbit s n U i hi]
  simp only [Matrix.mul_assoc, ← Matrix.mul_assoc (sectorWeightCanonicalUnitary i)ᴴ
    (sectorWeightCanonicalUnitary i), sectorWeightCanonicalUnitary_isometry,
    Matrix.one_mul, Matrix.mul_one]

def sectorOrbitForward (i : Sector d n)
    (F : MatrixChannel (IrrepIndex (sectorHighestOccupation i).val) M) :
    MatrixChannel (SectorSpace d n i) M :=
  F.comp (SchurProtocol.changeBasisChannel (sectorWeightCanonicalUnitary i)
    (sectorWeightCanonicalUnitary_isometry i))

def sectorOrbitReverse (i : Sector d n)
    (G : MatrixChannel M (IrrepIndex (sectorHighestOccupation i).val)) :
    MatrixChannel M (SectorSpace d n i) :=
  (SchurProtocol.changeBasisChannel (sectorWeightCanonicalUnitary i)ᴴ
    (by simpa using sectorWeightCanonicalUnitary_coisometry i)).comp G

theorem sectorOrbitForward_state (s : FixedSpectrum d r) (n : ℕ)
    (U : Matrix.unitaryGroup (Fin d) ℂ) (i : Sector d n) (hi : i ∈ physicalTypical s n)
    (F : MatrixChannel (IrrepIndex (sectorHighestOccupation i).val) M) :
    (sectorOrbitForward i F).toFun (physicalSectorState s n U i) =
      F.toFun (canonicalOrbitState s (sectorHighestOccupation i).val U) := by
  simp only [sectorOrbitForward, MatrixChannel.comp]
  rw [SchurProtocol.changeBasisChannel_apply, physicalSectorState_canonicalOrbit s n U i hi]

theorem sectorOrbitReverse_error (s : FixedSpectrum d r) (n : ℕ)
    (U : Matrix.unitaryGroup (Fin d) ℂ) (i : Sector d n) (hi : i ∈ physicalTypical s n)
    (G : MatrixChannel M (IrrepIndex (sectorHighestOccupation i).val))
    {τ : Matrix M M ℂ} (hτ : τ.PosSemidef) :
    traceDistance ((sectorOrbitReverse i G).toFun τ) (physicalSectorState s n U i) =
      traceDistance (G.toFun τ) (canonicalOrbitState s (sectorHighestOccupation i).val U) := by
  have hp : (canonicalOrbitState s (sectorHighestOccupation i).val U).PosSemidef := by
    rw [← physicalSectorState_canonicalOrbit s n U i hi]
    exact (physicalSectorState_positive s n U i).mul_mul_conjTranspose_same _
  simp only [sectorOrbitReverse, MatrixChannel.comp]
  rw [SchurProtocol.changeBasisChannel_apply, physicalSectorState_canonicalOrbit_pullback s n U i hi]
  have h := traceDistance_isometry (sectorWeightCanonicalUnitary i)ᴴ
    (by simpa using sectorWeightCanonicalUnitary_coisometry i) (G.positive _ hτ) hp
  simpa only [Matrix.conjTranspose_conjTranspose] using h

/-- Actual encoder on the tensor word space; independent of the orbit point U. -/
def physicalOrbitEncoder
    (F : ∀ i : Sector d n, MatrixChannel (IrrepIndex (sectorHighestOccupation i).val) M) :
    MatrixChannel (Fin n → Fin d) M := physicalEncoder (fun i => sectorOrbitForward i (F i))

/-- Actual decoder on the tensor word space, restoring the derived physical probabilities. -/
def physicalOrbitDecoder (s : FixedSpectrum d r) (n : ℕ)
    (G : ∀ i : Sector d n, MatrixChannel M (IrrepIndex (sectorHighestOccupation i).val)) :
    MatrixChannel M (Fin n → Fin d) := physicalDecoder s n (fun i => sectorOrbitReverse i (G i))

/-- Source-to-target estimate for the actual physical channel, using only
the individual canonical-orbit cloning estimates. -/
theorem physicalOrbit_forward_error_le (s : FixedSpectrum d r) (n : ℕ) (hn : 2 ≤ n)
    (F : ∀ i : Sector d n, MatrixChannel (IrrepIndex (sectorHighestOccupation i).val) M)
    (U : Matrix.unitaryGroup (Fin d) ℂ) (τ : Matrix M M ℂ)
    (hτ : τ.PosSemidef) (hτ1 : τ.trace = 1) (ε : ℝ) (hε : 0 ≤ ε)
    (hf : ∀ i ∈ physicalTypical s n,
      traceDistance ((F i).toFun (canonicalOrbitState s (sectorHighestOccupation i).val U)) τ ≤ ε) :
    traceDistance ((physicalOrbitEncoder F).toFun (TensorPowers.matrix n (physicalDensity s U))) τ ≤
      ε + Concentration.tailBound (concentrationExponent d + d) n := by
  apply physical_forward_error_le s n hn _ U τ hτ hτ1 ε hε
  intro i hi
  rw [sectorOrbitForward_state s n U i hi]
  exact hf i hi

/-- Target-to-source estimate for the actual physical channel, with all
representation and source-identification premises discharged. -/
theorem physicalOrbit_reverse_error_le (s : FixedSpectrum d r) (n : ℕ) (hn : 2 ≤ n)
    (G : ∀ i : Sector d n, MatrixChannel M (IrrepIndex (sectorHighestOccupation i).val))
    (U : Matrix.unitaryGroup (Fin d) ℂ) (τ : Matrix M M ℂ)
    (hτ : τ.PosSemidef) (hτ1 : τ.trace = 1) (ε : ℝ) (hε : 0 ≤ ε)
    (hr : ∀ i ∈ physicalTypical s n,
      traceDistance ((G i).toFun τ) (canonicalOrbitState s (sectorHighestOccupation i).val U) ≤ ε) :
    traceDistance ((physicalOrbitDecoder s n G).toFun τ) (TensorPowers.matrix n (physicalDensity s U)) ≤
      ε + Concentration.tailBound (concentrationExponent d + d) n := by
  apply physical_reverse_error_le s n hn _ U τ hτ hτ1 ε hε
  intro i hi
  rw [sectorOrbitReverse_error s n U i hi _ hτ]
  exact hr i hi

end FreeEntropy.SchurWeyl
