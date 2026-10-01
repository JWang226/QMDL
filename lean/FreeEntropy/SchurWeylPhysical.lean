/-
Copyright (c) 2026 Free Entropy formalization contributors.
See LICENSE and NOTICE in the repository root for license and attribution.
-/

import FreeEntropy.SchurWeylNormalization
import FreeEntropy.UnitaryDecomposition

/-!
# Unconditional orthogonal irreducible blocks of the physical mixed source

The representation decomposition is constructed by finite-dimensional
orthogonal induction. Its column matrices and sector actions are concrete.
The physical source block formula is derived by the unitary-bicommutant
argument, for every density matrix and every tensor power. No representation
existence, decomposition, source formula, or sector normalization is supplied.

Identifying these actual irreducible sectors with partition-labelled GT
modules and grouping equivalent sectors into labelled multiplicity spaces
are subsequent highest-weight classification tasks.
-/
noncomputable section
open scoped BigOperators ComplexOrder MatrixOrder
open Matrix
namespace FreeEntropy.SchurWeyl
open UnitaryDecomposition OrbitMemory
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000

/-- A constructed complete irreducible decomposition of the physical tensor action. -/
def physicalDecomposition (d n : ℕ) : Decomposition (physicalRepresentation d n) :=
  decomposition (physicalRepresentation d n) (physicalRepresentation_unitary d n)

abbrev Sector (d n : ℕ) := (physicalDecomposition d n).Index
abbrev SectorSpace (d n : ℕ) (i : Sector d n) := Fin ((physicalDecomposition d n).dimension i)

instance (d n : ℕ) (i : Sector d n) : Nonempty (SectorSpace d n i) :=
  Fin.pos_iff_nonempty.mp ((physicalDecomposition d n).dimension_pos i)

def physicalBlock {d : ℕ} (n : ℕ) (ρ : Matrix (Fin d) (Fin d) ℂ) (i : Sector d n) :
    Matrix (SectorSpace d n i) (SectorSpace d n i) ℂ :=
  ((physicalDecomposition d n).embedding i)ᴴ * TensorPowers.matrix n ρ *
    (physicalDecomposition d n).embedding i

def sectorProbability {d : ℕ} (n : ℕ) (ρ : Matrix (Fin d) (Fin d) ℂ) (i : Sector d n) : ℝ :=
  tr (physicalBlock n ρ i)

def sectorState {d : ℕ} (n : ℕ) (ρ : Matrix (Fin d) (Fin d) ℂ) (i : Sector d n) :
    Matrix (SectorSpace d n i) (SectorSpace d n i) ℂ := normalizedBlock (physicalBlock n ρ i)

/-- Every actual irreducible sector is positive for a positive physical source. -/
theorem physicalBlock_positive {d : ℕ} (n : ℕ) {ρ : Matrix (Fin d) (Fin d) ℂ}
    (hρ : ρ.PosSemidef) (i : Sector d n) : (physicalBlock n ρ i).PosSemidef :=
  source_compressed_positive _ hρ

theorem sectorProbability_nonneg {d : ℕ} (n : ℕ) {ρ : Matrix (Fin d) (Fin d) ℂ}
    (hρ : ρ.PosSemidef) (i : Sector d n) : 0 ≤ sectorProbability n ρ i :=
  (physicalBlock_positive n hρ i).trace_nonneg.1

theorem sectorState_positive {d : ℕ} (n : ℕ) {ρ : Matrix (Fin d) (Fin d) ℂ}
    (hρ : ρ.PosSemidef) (i : Sector d n) : (sectorState n ρ i).PosSemidef :=
  normalizedBlock_positive (physicalBlock_positive n hρ i)

theorem sectorState_trace {d : ℕ} (n : ℕ) {ρ : Matrix (Fin d) (Fin d) ℂ}
    (hρ : ρ.PosSemidef) (i : Sector d n) : (sectorState n ρ i).trace = 1 :=
  normalizedBlock_trace (physicalBlock_positive n hρ i)

/-- The literal mixed tensor-power source is the sum of its actually
constructed irreducible blocks. This theorem has no decomposition premise. -/
theorem physical_source_block_sum {d : ℕ} (n : ℕ) {ρ : Matrix (Fin d) (Fin d) ℂ}
    (hρ : ρ.IsHermitian) :
    TensorPowers.matrix n ρ = ∑ i : Sector d n,
      (physicalDecomposition d n).embedding i * physicalBlock n ρ i *
        ((physicalDecomposition d n).embedding i)ᴴ :=
  source_block_sum (physicalDecomposition d n).representation
    (physicalDecomposition d n).embedding (physicalDecomposition d n).isometry
    (physicalDecomposition d n).intertwines (physicalDecomposition d n).resolution hρ

/-- The physical mixed source is an actual normalized block mixture, with
zero-mass sectors handled by their explicit replacement states. -/
theorem physical_source_normalized_sum {d : ℕ} (n : ℕ) {ρ : Matrix (Fin d) (Fin d) ℂ}
    (hρ : ρ.PosSemidef) :
    TensorPowers.matrix n ρ = ∑ i : Sector d n, sectorProbability n ρ i •
      ((physicalDecomposition d n).embedding i * sectorState n ρ i *
        ((physicalDecomposition d n).embedding i)ᴴ) := by
  rw [physical_source_block_sum n hρ.isHermitian]
  apply Finset.sum_congr rfl
  intro i _
  rw [block_eq_trace_smul_normalized (physicalBlock_positive n hρ i),
    Matrix.mul_smul, Matrix.smul_mul]
  rfl

/-- The derived probabilities of all irreducible sectors sum to one. -/
theorem sectorProbability_sum {d : ℕ} (n : ℕ) {ρ : Matrix (Fin d) (Fin d) ℂ}
    (hρ : ρ.PosSemidef) (htrace : ρ.trace = 1) :
    ∑ i : Sector d n, sectorProbability n ρ i = 1 := by
  have ht := congrArg tr (physical_source_block_sum n hρ.isHermitian)
  rw [tr_sum] at ht
  have he (i : Sector d n) : tr ((physicalDecomposition d n).embedding i *
      physicalBlock n ρ i * ((physicalDecomposition d n).embedding i)ᴴ) =
      sectorProbability n ρ i := by
    unfold tr
    rw [Matrix.trace_mul_cycle, (physicalDecomposition d n).isometry, Matrix.one_mul]
    rfl
  simp only [he] at ht
  have hl : tr (TensorPowers.matrix n ρ) = 1 := by
    simp [tr, TensorPowers.matrix_trace, htrace]
  rw [hl] at ht
  exact ht.symm

/-- The square unitary transform obtained by assembling all actual sector bases. -/
def physicalBasis (d n : ℕ) : Matrix (Fin n → Fin d) (Σ i : Sector d n, SectorSpace d n i) ℂ :=
  fun w ia => (physicalDecomposition d n).embedding ia.1 w ia.2

theorem physicalBasis_isometry (d n : ℕ) : (physicalBasis d n)ᴴ * physicalBasis d n = 1 := by
  classical
  ext ⟨i, a⟩ ⟨j, b⟩
  change (((physicalDecomposition d n).embedding i)ᴴ *
    (physicalDecomposition d n).embedding j) a b = _
  by_cases hij : i = j
  · subst j
    rw [(physicalDecomposition d n).isometry]
    simp [Matrix.one_apply]
  · rw [(physicalDecomposition d n).orthogonal i j hij]
    simp [hij]

theorem physicalBasis_coisometry (d n : ℕ) : physicalBasis d n * (physicalBasis d n)ᴴ = 1 := by
  ext w v
  have h := congrFun (congrFun (physicalDecomposition d n).resolution w) v
  simpa only [physicalBasis, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Fintype.sum_sigma, Matrix.sum_apply] using h

/-- Exact block diagonalization of every physical Hermitian tensor power by
one constructed unitary basis, independent of the source matrix. -/
theorem physical_source_in_basis {d : ℕ} (n : ℕ) {ρ : Matrix (Fin d) (Fin d) ℂ}
    (hρ : ρ.IsHermitian) :
    (physicalBasis d n)ᴴ * TensorPowers.matrix n ρ * physicalBasis d n =
      Matrix.blockDiagonal' (physicalBlock n ρ) := by
  classical
  ext ⟨i, a⟩ ⟨j, b⟩
  change (((physicalDecomposition d n).embedding i)ᴴ * TensorPowers.matrix n ρ *
    (physicalDecomposition d n).embedding j) a b = _
  by_cases hij : i = j
  · subst j
    rw [Matrix.blockDiagonal'_apply_eq]
    rfl
  · rw [Matrix.blockDiagonal'_apply_ne _ _ _ hij,
      source_crossBlock_zero ((physicalDecomposition d n).representation j)
        ((physicalDecomposition d n).embedding i) ((physicalDecomposition d n).embedding j)
        ((physicalDecomposition d n).isometry j) ((physicalDecomposition d n).orthogonal i j hij)
        ((physicalDecomposition d n).intertwines j) hρ]
    rfl

end FreeEntropy.SchurWeyl
