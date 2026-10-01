/-
Copyright (c) 2026 Free Entropy formalization contributors.
See LICENSE and NOTICE in the repository root for license and attribution.
-/

import FreeEntropy.CartanChannel

/-!
# Concrete channels assembling sectors of different dimensions

Compression into mutually orthogonal sectors, followed by their individual
channels, gives an encoder into a common memory. A convex mixture of reverse
channels followed by the sector embeddings gives the decoder. Linearity,
trace preservation, and complete positivity at every finite amplification
are proved for these actual matrix formulas.
-/

noncomputable section
open scoped BigOperators Matrix Kronecker ComplexOrder MatrixOrder
open Matrix

namespace FreeEntropy.SectorChannels
open Channels

set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false

variable {ι S M : Type*} [Fintype ι] [Fintype S] [Fintype M]
  [DecidableEq ι] [DecidableEq S] [DecidableEq M]
variable {B : ι → Type*} [∀ i, Fintype (B i)] [∀ i, DecidableEq (B i)]

def compress {A C : Type*} [Fintype A] [Fintype C]
    (J : Matrix A C ℂ) (X : Matrix A A ℂ) : Matrix C C ℂ := Jᴴ * X * J

def embed {A C : Type*} [Fintype A] [Fintype C]
    (J : Matrix A C ℂ) (X : Matrix C C ℂ) : Matrix A A ℂ := J * X * Jᴴ

theorem compress_positive {A C : Type*} [Fintype A] [Fintype C]
    (J : Matrix A C ℂ) {X : Matrix A A ℂ} (hX : X.PosSemidef) :
    (compress J X).PosSemidef := by
  simpa only [compress, Matrix.conjTranspose_conjTranspose] using
    hX.mul_mul_conjTranspose_same Jᴴ

theorem embed_positive {A C : Type*} [Fintype A] [Fintype C]
    (J : Matrix A C ℂ) {X : Matrix C C ℂ} (hX : X.PosSemidef) :
    (embed J X).PosSemidef := hX.mul_mul_conjTranspose_same J

theorem compress_completely_positive {A C : Type*} [Fintype A] [Fintype C]
    (J : Matrix A C ℂ) (k : ℕ) {X : Matrix (Fin k × A) (Fin k × A) ℂ}
    (hX : X.PosSemidef) : (amplify (compress J) X).PosSemidef := by
  have heq : compress J = krausMap (fun _ : Unit => Jᴴ) := by
    funext Y
    simp [compress, krausMap]
  rw [heq]
  exact krausMap_completely_positive _ hX

theorem embed_completely_positive {A C : Type*} [Fintype A] [Fintype C]
    (J : Matrix A C ℂ) (k : ℕ) {X : Matrix (Fin k × C) (Fin k × C) ℂ}
    (hX : X.PosSemidef) : (amplify (embed J) X).PosSemidef := by
  have heq : embed J = krausMap (fun _ : Unit => J) := by
    funext Y
    simp [embed, krausMap]
  rw [heq]
  exact krausMap_completely_positive _ hX

theorem trace_embed {A C : Type*} [Fintype A] [Fintype C] [DecidableEq C]
    (J : Matrix A C ℂ) (hJ : Jᴴ * J = 1) (X : Matrix C C ℂ) :
    (embed J X).trace = X.trace := by
  unfold embed
  rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc, hJ, Matrix.one_mul]

/-- The actual encoder discards the sector label after applying its channel. -/
def encodeMap (J : ∀ i, Matrix S (B i) ℂ) (F : ∀ i, MatrixChannel (B i) M)
    (X : Matrix S S ℂ) : Matrix M M ℂ := ∑ i, (F i).toFun (compress (J i) X)

theorem encodeMap_trace (J : ∀ i, Matrix S (B i) ℂ)
    (F : ∀ i, MatrixChannel (B i) M) (hresolve : ∑ i, J i * (J i)ᴴ = 1)
    (X : Matrix S S ℂ) : (encodeMap J F X).trace = X.trace := by
  calc
    _ = ∑ i, ((J i * (J i)ᴴ) * X).trace := by
      simp only [encodeMap, Matrix.trace_sum, MatrixChannel.trace_preserving, compress]
      apply Finset.sum_congr rfl
      intro i _
      rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc]
    _ = ((∑ i, J i * (J i)ᴴ) * X).trace := by
      rw [Matrix.sum_mul, Matrix.trace_sum]
    _ = X.trace := by rw [hresolve, Matrix.one_mul]

theorem encodeMap_completely_positive (J : ∀ i, Matrix S (B i) ℂ)
    (F : ∀ i, MatrixChannel (B i) M) (k : ℕ)
    {X : Matrix (Fin k × S) (Fin k × S) ℂ} (hX : X.PosSemidef) :
    (amplify (encodeMap J F) X).PosSemidef := by
  have heq : amplify (encodeMap J F) X =
      ∑ i, amplify (F i).toFun (amplify (compress (J i)) X) := by
    ext a b
    simp [amplify, encodeMap, Matrix.sum_apply]
  rw [heq]
  apply Matrix.posSemidef_sum
  intro i _
  exact (F i).completely_positive k _ (compress_completely_positive (J i) k hX)

/-- The resolution of the identity is exactly what makes the assembled
encoder trace preserving. Individual sector dimensions may differ. -/
def encoder (J : ∀ i, Matrix S (B i) ℂ) (F : ∀ i, MatrixChannel (B i) M)
    (hresolve : ∑ i, J i * (J i)ᴴ = 1) : MatrixChannel S M where
  toFun := encodeMap J F
  map_add := by
    intro X Y
    simp only [encodeMap, compress, Matrix.mul_add, Matrix.add_mul,
      MatrixChannel.map_add, Finset.sum_add_distrib]
  map_smul := by
    intro c X
    simp only [encodeMap, compress, Matrix.mul_smul, Matrix.smul_mul,
      MatrixChannel.map_smul, Finset.smul_sum]
  trace_preserving := encodeMap_trace J F hresolve
  positive := by
    intro X hX
    exact Matrix.posSemidef_sum _ (fun i _ => (F i).positive _ (compress_positive (J i) hX))
  completely_positive := encodeMap_completely_positive J F

/-- The decoder chooses its sector with prescribed classical probabilities. -/
def decodeMap (J : ∀ i, Matrix S (B i) ℂ) (G : ∀ i, MatrixChannel M (B i))
    (q : ι → ℝ) (Y : Matrix M M ℂ) : Matrix S S ℂ :=
  ∑ i, q i • embed (J i) ((G i).toFun Y)

theorem decodeMap_trace (J : ∀ i, Matrix S (B i) ℂ)
    (G : ∀ i, MatrixChannel M (B i)) (q : ι → ℝ)
    (hJ : ∀ i, (J i)ᴴ * J i = 1) (hq : ∑ i, q i = 1) (Y : Matrix M M ℂ) :
    (decodeMap J G q Y).trace = Y.trace := by
  simp only [decodeMap, Matrix.trace_sum, Matrix.trace_smul, trace_embed _ (hJ _),
    MatrixChannel.trace_preserving]
  rw [← Finset.sum_smul, hq, one_smul]

theorem decodeMap_completely_positive (J : ∀ i, Matrix S (B i) ℂ)
    (G : ∀ i, MatrixChannel M (B i)) (q : ι → ℝ) (hq : ∀ i, 0 ≤ q i) (k : ℕ)
    {Y : Matrix (Fin k × M) (Fin k × M) ℂ} (hY : Y.PosSemidef) :
    (amplify (decodeMap J G q) Y).PosSemidef := by
  have heq : amplify (decodeMap J G q) Y =
      ∑ i, q i • amplify (embed (J i)) (amplify (G i).toFun Y) := by
    ext a b
    simp [amplify, decodeMap, Matrix.sum_apply, Matrix.smul_apply]
  rw [heq]
  apply Matrix.posSemidef_sum
  intro i _
  exact (embed_completely_positive (J i) k ((G i).completely_positive k _ hY)).smul (hq i)

/-- The actual convex-mixture decoder, including its complete positivity. -/
def decoder (J : ∀ i, Matrix S (B i) ℂ) (G : ∀ i, MatrixChannel M (B i))
    (q : ι → ℝ) (hJ : ∀ i, (J i)ᴴ * J i = 1)
    (hq0 : ∀ i, 0 ≤ q i) (hq1 : ∑ i, q i = 1) : MatrixChannel M S where
  toFun := decodeMap J G q
  map_add := by
    intro X Y
    simp only [decodeMap, MatrixChannel.map_add, embed, Matrix.mul_add, Matrix.add_mul,
      smul_add, Finset.sum_add_distrib]
  map_smul := by
    intro c X
    simp only [decodeMap, MatrixChannel.map_smul, embed, Matrix.mul_smul, Matrix.smul_mul,
      smul_comm (q _) c, Finset.smul_sum]
  trace_preserving := decodeMap_trace J G q hJ hq1
  positive := by
    intro Y hY
    exact Matrix.posSemidef_sum _
      (fun i _ => (embed_positive (J i) ((G i).positive _ hY)).smul (hq0 i))
  completely_positive := decodeMap_completely_positive J G q hq0

theorem encoder_apply (J : ∀ i, Matrix S (B i) ℂ) (F : ∀ i, MatrixChannel (B i) M)
    (hresolve : ∑ i, J i * (J i)ᴴ = 1) (X : Matrix S S ℂ) :
    (encoder J F hresolve).toFun X = ∑ i, (F i).toFun (compress (J i) X) := rfl

theorem decoder_apply (J : ∀ i, Matrix S (B i) ℂ) (G : ∀ i, MatrixChannel M (B i))
    (q : ι → ℝ) (hJ : ∀ i, (J i)ᴴ * J i = 1)
    (hq0 : ∀ i, 0 ≤ q i) (hq1 : ∑ i, q i = 1) (Y : Matrix M M ℂ) :
    (decoder J G q hJ hq0 hq1).toFun Y = ∑ i, q i • embed (J i) ((G i).toFun Y) := rfl

theorem compress_embed_same {A C : Type*} [Fintype A] [Fintype C] [DecidableEq C]
    (J : Matrix A C ℂ) (hJ : Jᴴ * J = 1) (X : Matrix C C ℂ) :
    compress J (embed J X) = X := by
  change Jᴴ * (J * X * Jᴴ) * J = X
  calc
    _ = (Jᴴ * J) * X * (Jᴴ * J) := by simp only [Matrix.mul_assoc]
    _ = X := by rw [hJ, Matrix.one_mul, Matrix.mul_one]

theorem compress_embed_other {A C D : Type*} [Fintype A] [Fintype C] [Fintype D]
    (J : Matrix A C ℂ) (K : Matrix A D ℂ) (hJK : Jᴴ * K = 0) (X : Matrix D D ℂ) :
    compress J (embed K X) = 0 := by
  change Jᴴ * (K * X * Kᴴ) * J = 0
  calc
    _ = (Jᴴ * K) * X * (Kᴴ * J) := by simp only [Matrix.mul_assoc]
    _ = 0 := by rw [hJK, Matrix.zero_mul, Matrix.zero_mul]

theorem compress_smul {A C : Type*} [Fintype A] [Fintype C]
    (J : Matrix A C ℂ) (p : ℝ) (X : Matrix A A ℂ) :
    compress J (p • X) = p • compress J X := by
  simp only [compress, Matrix.mul_smul, Matrix.smul_mul]

theorem compress_sum {A C T : Type*} [Fintype A] [Fintype C] [Fintype T]
    (J : Matrix A C ℂ) (X : T → Matrix A A ℂ) :
    compress J (∑ i, X i) = ∑ i, compress J (X i) := by
  simp only [compress, Matrix.mul_sum, Matrix.sum_mul]

/-- Orthogonality extracts exactly one block, even when the sectors have
different dimensions. The coefficients need not be probabilities here. -/
theorem compress_block_mixture (J : ∀ i, Matrix S (B i) ℂ)
    (hJ : ∀ i, (J i)ᴴ * J i = 1)
    (horth : ∀ i j, i ≠ j → (J i)ᴴ * J j = 0)
    (p : ι → ℝ) (σ : ∀ i, Matrix (B i) (B i) ℂ) (i : ι) :
    compress (J i) (∑ j, p j • embed (J j) (σ j)) = p i • σ i := by
  rw [compress_sum]
  simp_rw [compress_smul]
  rw [Finset.sum_eq_single i]
  · rw [compress_embed_same _ (hJ i)]
  · intro j _ hji
    rw [compress_embed_other _ _ (horth i j hji.symm), smul_zero]
  · exact fun hnot => (hnot (Finset.mem_univ i)).elim

/-- The assembled encoder acts on a block mixture by the corresponding
mixture of its individual sector outputs. -/
theorem encodeMap_block_mixture (J : ∀ i, Matrix S (B i) ℂ)
    (F : ∀ i, MatrixChannel (B i) M)
    (hJ : ∀ i, (J i)ᴴ * J i = 1)
    (horth : ∀ i j, i ≠ j → (J i)ᴴ * J j = 0)
    (p : ι → ℝ) (σ : ∀ i, Matrix (B i) (B i) ℂ) :
    encodeMap J F (∑ j, p j • embed (J j) (σ j)) = ∑ i, p i • (F i).toFun (σ i) := by
  unfold encodeMap
  simp_rw [compress_block_mixture J hJ horth]
  apply Finset.sum_congr rfl
  intro i _
  exact (F i).toRealLinearMap.map_smul (p i) (σ i)

theorem encoder_block_mixture (J : ∀ i, Matrix S (B i) ℂ)
    (F : ∀ i, MatrixChannel (B i) M) (hresolve : ∑ i, J i * (J i)ᴴ = 1)
    (hJ : ∀ i, (J i)ᴴ * J i = 1)
    (horth : ∀ i j, i ≠ j → (J i)ᴴ * J j = 0)
    (p : ι → ℝ) (σ : ∀ i, Matrix (B i) (B i) ℂ) :
    (encoder J F hresolve).toFun (∑ j, p j • embed (J j) (σ j)) =
      ∑ i, p i • (F i).toFun (σ i) := encodeMap_block_mixture J F hJ horth p σ

/-- Explicit source-to-memory-to-source formula for the constructed channels. -/
theorem roundtrip_block_mixture (J : ∀ i, Matrix S (B i) ℂ)
    (F : ∀ i, MatrixChannel (B i) M) (G : ∀ i, MatrixChannel M (B i))
    (hresolve : ∑ i, J i * (J i)ᴴ = 1) (hJ : ∀ i, (J i)ᴴ * J i = 1)
    (horth : ∀ i j, i ≠ j → (J i)ᴴ * J j = 0)
    (p q : ι → ℝ) (hq0 : ∀ i, 0 ≤ q i) (hq1 : ∑ i, q i = 1)
    (σ : ∀ i, Matrix (B i) (B i) ℂ) :
    (decoder J G q hJ hq0 hq1).toFun
      ((encoder J F hresolve).toFun (∑ j, p j • embed (J j) (σ j))) =
      ∑ i, q i • embed (J i) ((G i).toFun (∑ j, p j • (F j).toFun (σ j))) := by
  rw [encoder_block_mixture J F hresolve hJ horth, decoder_apply]

/-- Canonical inclusions into the dependent direct sum of all sectors. -/
def sectorEmbedding (i : ι) : Matrix (Σ j, B j) (B i) ℂ :=
  fun a b => if a = ⟨i, b⟩ then 1 else 0

theorem sectorEmbedding_isometry (i : ι) :
    (sectorEmbedding (B := B) i)ᴴ * sectorEmbedding (B := B) i = 1 := by
  ext b c
  simp [sectorEmbedding, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Matrix.one_apply, eq_comm]

theorem sectorEmbedding_orthogonal (i j : ι) (hij : i ≠ j) :
    (sectorEmbedding (B := B) i)ᴴ * sectorEmbedding (B := B) j = 0 := by
  ext b c
  simp [sectorEmbedding, Matrix.mul_apply, Matrix.conjTranspose_apply, hij.symm]

theorem sectorEmbedding_resolution :
    (∑ i, sectorEmbedding (B := B) i * (sectorEmbedding (B := B) i)ᴴ) = 1 := by
  ext a b
  simp only [Matrix.sum_apply, Matrix.mul_apply, sectorEmbedding, Matrix.conjTranspose_apply,
    apply_ite star, star_one, star_zero]
  rw [← Fintype.sum_sigma (fun x : Sigma B =>
    (if a = x then (1 : ℂ) else 0) * (if b = x then 1 else 0))]
  simp [Matrix.one_apply]

/-- An encoder on the actual dependent direct sum requires only the sector
channels; all isometry and resolution identities are supplied above. -/
def directSumEncoder (F : ∀ i, MatrixChannel (B i) M) : MatrixChannel (Σ i, B i) M :=
  encoder sectorEmbedding F sectorEmbedding_resolution

/-- The matching decoder on the actual dependent direct sum. -/
def directSumDecoder (G : ∀ i, MatrixChannel M (B i)) (q : ι → ℝ)
    (hq0 : ∀ i, 0 ≤ q i) (hq1 : ∑ i, q i = 1) : MatrixChannel M (Σ i, B i) :=
  decoder sectorEmbedding G q sectorEmbedding_isometry hq0 hq1

end FreeEntropy.SectorChannels
