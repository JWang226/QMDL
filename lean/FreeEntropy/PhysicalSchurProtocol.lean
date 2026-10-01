/-
Copyright (c) 2026 Free Entropy formalization contributors.
See LICENSE and NOTICE in the repository root for license and attribution.
-/

import FreeEntropy.SchurWeylConcentration
import FreeEntropy.SectorProtocol
import FreeEntropy.SchurAchievability

/-! The Schur encoder and decoder are now actual channels on the literal
physical word space. Their source decomposition and atypical tail are
proved, not supplied. Only the local channels are parameters to this
assembly; concrete cloning channels can be substituted directly. -/
noncomputable section
open Matrix Filter
open scoped BigOperators Topology ComplexOrder MatrixOrder
namespace FreeEntropy.SchurWeyl
open Channels TraceDistance
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
attribute [local instance] Classical.propDecidable
variable {d r n : ℕ}
variable {M : Type*} [Fintype M] [DecidableEq M]

def physicalDensity (s : FixedSpectrum d r) (U : Matrix.unitaryGroup (Fin d) ℂ) :
    Matrix (Fin d) (Fin d) ℂ :=
  (U : Matrix (Fin d) (Fin d) ℂ) * Matrix.diagonal (fun j => (physicalSpectrum s j : ℂ)) *
    (U : Matrix (Fin d) (Fin d) ℂ)ᴴ

theorem physicalDiagonal_positive (s : FixedSpectrum d r) :
    (Matrix.diagonal (fun j => (physicalSpectrum s j : ℂ))).PosSemidef :=
  Matrix.PosSemidef.diagonal (fun j => Complex.zero_le_real.mpr (physicalSpectrum_nonneg s j))

theorem physicalDiagonal_trace (s : FixedSpectrum d r) :
    (Matrix.diagonal (fun j => (physicalSpectrum s j : ℂ))).trace = 1 := by
  rw [Matrix.trace_diagonal, ← Complex.ofReal_sum, physicalSpectrum_normalized]
  rfl

theorem physicalDensity_positive (s : FixedSpectrum d r) (U : Matrix.unitaryGroup (Fin d) ℂ) :
    (physicalDensity s U).PosSemidef :=
  (physicalDiagonal_positive s).mul_mul_conjTranspose_same U.val

theorem physicalDensity_trace (s : FixedSpectrum d r) (U : Matrix.unitaryGroup (Fin d) ℂ) :
    (physicalDensity s U).trace = 1 := by
  rw [physicalDensity, Matrix.trace_mul_cycle, show (U : Matrix (Fin d) (Fin d) ℂ)ᴴ * U = 1 from
    Matrix.UnitaryGroup.star_mul_self U, Matrix.one_mul]
  exact physicalDiagonal_trace s

/-- Actual source-sector probabilities, independent of the unknown orbit point. -/
def physicalProbability (s : FixedSpectrum d r) (n : ℕ) (i : Sector d n) : ℝ :=
  sectorProbability n (Matrix.diagonal (fun j => (physicalSpectrum s j : ℂ))) i

theorem physicalProbability_nonneg (s : FixedSpectrum d r) (n : ℕ) (i : Sector d n) :
    0 ≤ physicalProbability s n i := sectorProbability_nonneg n (physicalDiagonal_positive s) i

theorem physicalProbability_sum (s : FixedSpectrum d r) (n : ℕ) :
    ∑ i : Sector d n, physicalProbability s n i = 1 :=
  sectorProbability_sum n (physicalDiagonal_positive s) (physicalDiagonal_trace s)

def physicalSectorState (s : FixedSpectrum d r) (n : ℕ)
    (U : Matrix.unitaryGroup (Fin d) ℂ) (i : Sector d n) :
    Matrix (SectorSpace d n i) (SectorSpace d n i) ℂ := sectorState n (physicalDensity s U) i

theorem physicalSectorState_positive (s : FixedSpectrum d r) (n : ℕ)
    (U : Matrix.unitaryGroup (Fin d) ℂ) (i : Sector d n) :
    (physicalSectorState s n U i).PosSemidef :=
  sectorState_positive n (physicalDensity_positive s U) i

theorem physicalSectorState_trace (s : FixedSpectrum d r) (n : ℕ)
    (U : Matrix.unitaryGroup (Fin d) ℂ) (i : Sector d n) :
    (physicalSectorState s n U i).trace = 1 :=
  sectorState_trace n (physicalDensity_positive s U) i

/-- Exact mixture identity for the actual tensor-power source, including
every multiplicity copy and zero-probability summand. -/
theorem physical_source_mixture (s : FixedSpectrum d r) (n : ℕ)
    (U : Matrix.unitaryGroup (Fin d) ℂ) :
    TensorPowers.matrix n (physicalDensity s U) = ∑ i : Sector d n,
      physicalProbability s n i • SectorChannels.embed ((physicalDecomposition d n).embedding i)
        (physicalSectorState s n U i) := by
  rw [physical_source_normalized_sum n (physicalDensity_positive s U)]
  apply Finset.sum_congr rfl
  intro i _
  rw [show sectorProbability n (physicalDensity s U) i = physicalProbability s n i from
    sectorProbability_unitary_conjugate i U _]
  rfl

/-- Actual physical compression. It measures the proved orthogonal sectors
and applies the chosen local channel, discarding the sector label. -/
def physicalEncoder (F : ∀ i : Sector d n, MatrixChannel (SectorSpace d n i) M) :
    MatrixChannel (Fin n → Fin d) M :=
  SectorChannels.encoder (physicalDecomposition d n).embedding F
    (physicalDecomposition d n).resolution

/-- Actual physical decompression, restoring each copy with its derived
physical probability. Both maps are independent of the unknown unitary. -/
def physicalDecoder (s : FixedSpectrum d r) (n : ℕ)
    (G : ∀ i : Sector d n, MatrixChannel M (SectorSpace d n i)) :
    MatrixChannel M (Fin n → Fin d) :=
  SectorChannels.decoder (physicalDecomposition d n).embedding G (physicalProbability s n)
    (physicalDecomposition d n).isometry (physicalProbability_nonneg s n) (physicalProbability_sum s n)

def physicalTypical (s : FixedSpectrum d r) (n : ℕ) : Finset (Sector d n) :=
  Finset.univ.filter (fun i => TypicalRows.Typical s n (occupationRow (sectorHighestOccupation i)))

theorem physical_outsideMass (s : FixedSpectrum d r) (n : ℕ) :
    Protocol.outsideMass Finset.univ (physicalTypical s n) (physicalProbability s n) =
      physicalAtypicalMass s n := by
  unfold Protocol.outsideMass physicalTypical physicalAtypicalMass physicalProbability
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro i _
  by_cases h : TypicalRows.Typical s n (occupationRow (sectorHighestOccupation i)) <;>
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, h, not_true_eq_false,
      not_false_eq_true, ite_true, ite_false]

/-- Finite actual-source error bound: the source identity, channels,
probabilities, and concentration estimate are all instantiated concretely. -/
theorem physical_roundtrip_error_le (s : FixedSpectrum d r) (n : ℕ) (hn : 2 ≤ n)
    (F : ∀ i : Sector d n, MatrixChannel (SectorSpace d n i) M)
    (G : ∀ i : Sector d n, MatrixChannel M (SectorSpace d n i))
    (U : Matrix.unitaryGroup (Fin d) ℂ) (τ : Matrix M M ℂ)
    (hτ : τ.PosSemidef) (hτ1 : τ.trace = 1) (ε : ℝ) (hε : 0 ≤ ε)
    (hf : ∀ i ∈ physicalTypical s n,
      traceDistance ((F i).toFun (physicalSectorState s n U i)) τ ≤ ε)
    (hr : ∀ i ∈ physicalTypical s n,
      traceDistance ((G i).toFun τ) (physicalSectorState s n U i) ≤ ε) :
    traceDistance ((physicalDecoder s n G).toFun ((physicalEncoder F).toFun
      (TensorPowers.matrix n (physicalDensity s U))))
      (TensorPowers.matrix n (physicalDensity s U)) ≤
        2 * ε + 2 * Concentration.tailBound (concentrationExponent d + d) n := by
  have h := SectorProtocol.typical_sector_roundtrip_error (physicalDecomposition d n).embedding
    F G (physicalDecomposition d n).resolution (physicalDecomposition d n).isometry
    (physicalDecomposition d n).orthogonal (physicalProbability s n)
    (physicalProbability_nonneg s n) (physicalProbability_sum s n)
    (physicalSectorState s n U) (physicalSectorState_positive s n U) (physicalSectorState_trace s n U)
    τ hτ hτ1 (physicalTypical s n) ε hε hf hr
  rw [← physical_source_mixture, physical_outsideMass] at h
  exact h.trans (by linarith [physicalAtypicalMass_le_tailBound s n hn])

end FreeEntropy.SchurWeyl
