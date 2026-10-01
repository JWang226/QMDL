/-
Copyright (c) 2026 Free Entropy formalization contributors.
See LICENSE and NOTICE in the repository root for license and attribution.
-/

import FreeEntropy.CloningMatrices
import FreeEntropy.CartanChannel
import FreeEntropy.CartanBalance
import FreeEntropy.ProjectorGeometry

/-!
# Realizing the cloning block model by actual Cartan channels

The adapter constructs the CPTP maps and both compressed block families.
Its remaining inputs are the representation projectors, their traces and
normalization, the local weight-sector identities, and the ambient projector
norm estimate. No aggregate channel branch inequality or error bound is
assumed. The source, target, and auxiliary dimensions may all differ.
-/

noncomputable section
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator Kronecker
open Matrix FreeEntropy.OrbitMemory FreeEntropy.CloningMatrices
open FreeEntropy.CartanChannel

namespace FreeEntropy.CartanCloning

set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 600000

variable {A B C T ι : Type*}
  [Fintype A] [Fintype B] [Fintype C] [Fintype T]
  [DecidableEq A] [DecidableEq B] [DecidableEq C] [DecidableEq T]

theorem isometry_pullback (V : Matrix T C ℂ) (hV : Vᴴ * V = 1)
    (X : Matrix C C ℂ) : Vᴴ * (V * X * Vᴴ) * V = X := by
  calc
    _ = (Vᴴ * V) * X * (Vᴴ * V) := by simp only [Matrix.mul_assoc]
    _ = _ := by rw [hV]; simp

theorem range_pullback (V : Matrix T C ℂ) (hV : Vᴴ * V = 1)
    (X : Matrix T T ℂ) : Vᴴ * ((V * Vᴴ) * X * (V * Vᴴ)) * V = Vᴴ * X * V := by
  calc
    _ = (Vᴴ * V) * Vᴴ * X * V * (Vᴴ * V) := by simp only [Matrix.mul_assoc]
    _ = _ := by rw [hV]; simp

theorem isStarProjection_embedding (V : Matrix T C ℂ) (hV : Vᴴ * V = 1)
    {P : Matrix C C ℂ} (hP : IsStarProjection P) : IsStarProjection (V * P * Vᴴ) := by
  apply isStarProjection_iff'.mpr
  constructor
  · calc
      _ = V * P * (Vᴴ * V) * P * Vᴴ := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [hV, Matrix.mul_one, Matrix.mul_assoc V P P, hP.isIdempotentElem.eq]
  · change (V * P * Vᴴ)ᴴ = _
    have hPH : Pᴴ = P := hP.isSelfAdjoint.star_eq
    simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
      hPH, Matrix.mul_assoc]

theorem rectangular_compression_mono {X Y : Matrix T T ℂ} (h : X ≤ Y)
    (J : Matrix T C ℂ) : Jᴴ * X * J ≤ Jᴴ * Y * J := by
  apply Matrix.le_iff.mpr
  simpa only [Matrix.mul_sub, Matrix.sub_mul] using
    (Matrix.le_iff.mp h).conjTranspose_mul_mul_same J

/-- The unembedded version of the retained forward branch. -/
theorem forward_branch_unembedded (V : Matrix (A × B) C ℂ) (hV : Vᴴ * V = 1)
    (k : B) (din dout : ℝ) (hr : 0 ≤ din / dout)
    {σ : Matrix A A ℂ} (hσ : σ.PosSemidef) :
    (din / dout) • (Vᴴ * basisEmbedding (A := A) k * σ *
      (basisEmbedding (A := A) k)ᴴ * V) ≤ sectorMap din dout V σ := by
  have h := rectangular_compression_mono (forward_retained_branch_le V k din dout hr hσ) V
  rw [isometry_pullback V hV] at h
  rw [Matrix.mul_smul, Matrix.smul_mul] at h
  have heq : Vᴴ * ((V * Vᴴ) * basisEmbedding (A := A) k * σ *
      (basisEmbedding (A := A) k)ᴴ * (V * Vᴴ)) * V =
      Vᴴ * basisEmbedding (A := A) k * σ * (basisEmbedding (A := A) k)ᴴ * V := by
    calc
      _ = Vᴴ * ((V * Vᴴ) * (basisEmbedding (A := A) k * σ *
          (basisEmbedding (A := A) k)ᴴ) * (V * Vᴴ)) * V := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [range_pullback V hV]; simp only [Matrix.mul_assoc]
  rwa [heq] at h

/-- Construct the finite block realization in the original source and
target spaces. The ambient projectors are `V Pν V†` and `J Pμ J†`.

The local sector identities are precisely what the weight decomposition
supplies: the full Cartan range compresses `Qδ` to `Pδ Qδ Pδ`, and fixing
the auxiliary highest weight restricts the reverse block to `Qδ`.
-/
def ofWeightBlocks (s : Finset ι) (m n : ι → ℕ) (pμ pν e : ι → ℝ)
    (Pμ : ι → Matrix A A ℂ) (Pν : ι → Matrix C C ℂ)
    (V : Matrix (A × B) C ℂ) (hV : Vᴴ * V = 1) (k : B)
    (din dout : ℝ) (hdin : 0 < din) (hdout : 0 < dout)
    (hbalance : partialTrace (V * Vᴴ) = (dout / din) • (1 : Matrix A A ℂ))
    (hpμ : ∀ i ∈ s, 0 ≤ pμ i) (hpν : ∀ i ∈ s, 0 ≤ pν i)
    (hPμ : ∀ i ∈ s, IsStarProjection (Pμ i))
    (hPν : ∀ i ∈ s, IsStarProjection (Pν i))
    (htrμ : ∀ i ∈ s, tr (Pμ i) = (m i : ℝ))
    (htrν : ∀ i ∈ s, tr (Pν i) = (n i : ℝ))
    (hnormμ : (mixture s pμ Pμ).trace = 1)
    (hnormν : (mixture s pν Pν).trace = 1)
    (hclose : ∀ i ∈ s,
      ‖V * Pν i * Vᴴ - basisEmbedding (A := A) k * Pμ i *
        (basisEmbedding (A := A) k)ᴴ‖ ^ 2 ≤ e i)
    (hforward_sector : ∀ i ∈ s,
      (V * Vᴴ) * (basisEmbedding (A := A) k * Pμ i * (basisEmbedding (A := A) k)ᴴ) * (V * Vᴴ) =
      (V * Pν i * Vᴴ) * (basisEmbedding (A := A) k * Pμ i * (basisEmbedding (A := A) k)ᴴ) *
        (V * Pν i * Vᴴ))
    (hreverse_sector : ∀ i ∈ s,
      (basisEmbedding (A := A) k)ᴴ * (V * Pν i * Vᴴ) * basisEmbedding (A := A) k =
      (basisEmbedding (A := A) k)ᴴ *
        ((basisEmbedding (A := A) k * Pμ i * (basisEmbedding (A := A) k)ᴴ) *
          (V * Pν i * Vᴴ) * (basisEmbedding (A := A) k * Pμ i * (basisEmbedding (A := A) k)ᴴ)) *
        basisEmbedding (A := A) k) :
    BlockRealization s m n pμ pν e (din / dout) A C := by
  let J := basisEmbedding (A := A) k
  let P : ι → Matrix (A × B) (A × B) ℂ := fun i => V * Pν i * Vᴴ
  let Q : ι → Matrix (A × B) (A × B) ℂ := fun i => J * Pμ i * Jᴴ
  have hJ : Jᴴ * J = 1 := basisEmbedding_isometry k
  have hP (i) (hi : i ∈ s) : IsStarProjection (P i) := isStarProjection_embedding V hV (hPν i hi)
  have hQ (i) (hi : i ∈ s) : IsStarProjection (Q i) := isStarProjection_embedding J hJ (hPμ i hi)
  have hμpos (i) (hi : i ∈ s) : (Pμ i).PosSemidef := (hPμ i hi).nonneg.posSemidef
  have hνpos (i) (hi : i ∈ s) : (Pν i).PosSemidef := (hPν i hi).nonneg.posSemidef
  refine {
    Pμ := Pμ
    Pν := Pν
    Cμ := fun i => Jᴴ * (Q i * P i * Q i) * J
    Cν := fun i => Vᴴ * (P i * Q i * P i) * V
    forward := cartanChannel V din dout hdin hdout hbalance
    reverse := reverseChannel V hV
    positive_μ := hμpos
    positive_ν := hνpos
    compressed_positive_ν := ?_
    trace_μ := htrμ
    trace_ν := htrν
    normalized_μ := hnormμ
    normalized_ν := hnormν
    block_μ := ?_
    block_ν := ?_
    branch_forward := ?_
    branch_reverse := ?_ }
  · intro i hi
    have h := (hQ i hi).nonneg.posSemidef.mul_mul_conjTranspose_same (P i)
    have hPH : (P i)ᴴ = P i := (hP i hi).isSelfAdjoint.star_eq
    rw [hPH] at h
    exact h.conjTranspose_mul_mul_same V
  · intro i hi
    have h := rectangular_compression_mono
      (ProjectorGeometry.projector_block_bounds (hP i hi) (hQ i hi) (hclose i hi)).2 J
    simpa only [Matrix.mul_smul, Matrix.smul_mul, Q, isometry_pullback J hJ] using h
  · intro i hi
    have h := rectangular_compression_mono
      (ProjectorGeometry.projector_block_bounds (hP i hi) (hQ i hi) (hclose i hi)).1 V
    simpa only [Matrix.mul_smul, Matrix.smul_mul, P, isometry_pullback V hV] using h
  · rw [cartanChannel_apply]
    have h := forward_branch_unembedded V hV k din dout (le_of_lt (div_pos hdin hdout))
      (mixture_positive s pμ Pμ hpμ hμpos)
    have hid : mixture s pμ (fun i => Vᴴ * (P i * Q i * P i) * V) =
        Vᴴ * J * mixture s pμ Pμ * Jᴴ * V := by
      calc
        _ = mixture s pμ (fun i => Vᴴ * Q i * V) := by
          apply Finset.sum_congr rfl
          intro i hi
          congr 1
          change Vᴴ * (P i * Q i * P i) * V = Vᴴ * Q i * V
          have hsector : (V * Vᴴ) * Q i * (V * Vᴴ) = P i * Q i * P i := hforward_sector i hi
          rw [← hsector, range_pullback V hV]
        _ = _ := by
          simp only [mixture, Q, Matrix.mul_sum, Matrix.sum_mul,
            Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc]
    rw [hid]
    exact h
  · rw [reverseChannel_apply]
    have h := reverse_retained_branch_le V k (mixture_positive s pν Pν hpν hνpos)
    have hid : mixture s pν (fun i => Jᴴ * (Q i * P i * Q i) * J) =
        Jᴴ * V * mixture s pν Pν * Vᴴ * J := by
      calc
        _ = mixture s pν (fun i => Jᴴ * P i * J) := by
          apply Finset.sum_congr rfl
          intro i hi
          congr 1
          exact (hreverse_sector i hi).symm
        _ = _ := by
          simp only [mixture, P, Matrix.mul_sum, Matrix.sum_mul,
            Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc]
    rw [hid]
    exact h

/-- The strongest channel-construction adapter: genuine representation
irreducibility and unitary intertwining discharge the normalization balance.
The channel coefficient uses the actual finite dimensions. Connecting these
to the Weyl products still requires the representation dimension formula.
No arbitrary balance or scalarity premise appears in this constructor. -/
def ofWeightBlocksOfIrreducible {G : Type*} [Group G] [Nonempty A] [Nonempty C]
    (UA : G →* Matrix A A ℂ) (UB : G →* Matrix B B ℂ) (UC : G →* Matrix C C ℂ)
    [Representation.IsIrreducible (Twirling.matrixRepresentation UA)]
    (hUA : ∀ g, (UA g)ᴴ * UA g = 1)
    (hUB : ∀ g, (UB g)ᴴ * UB g = 1)
    (hUC : ∀ g, (UC g)ᴴ * UC g = 1)
    (s : Finset ι) (m n : ι → ℕ) (pμ pν e : ι → ℝ)
    (Pμ : ι → Matrix A A ℂ) (Pν : ι → Matrix C C ℂ)
    (V : Matrix (A × B) C ℂ) (hV : Vᴴ * V = 1) (k : B)
    (hintertwine : ∀ g, (UA g ⊗ₖ UB g) * V = V * UC g)
    (hpμ : ∀ i ∈ s, 0 ≤ pμ i) (hpν : ∀ i ∈ s, 0 ≤ pν i)
    (hPμ : ∀ i ∈ s, IsStarProjection (Pμ i))
    (hPν : ∀ i ∈ s, IsStarProjection (Pν i))
    (htrμ : ∀ i ∈ s, tr (Pμ i) = (m i : ℝ))
    (htrν : ∀ i ∈ s, tr (Pν i) = (n i : ℝ))
    (hnormμ : (mixture s pμ Pμ).trace = 1)
    (hnormν : (mixture s pν Pν).trace = 1)
    (hclose : ∀ i ∈ s,
      ‖V * Pν i * Vᴴ - basisEmbedding (A := A) k * Pμ i *
        (basisEmbedding (A := A) k)ᴴ‖ ^ 2 ≤ e i)
    (hforward_sector : ∀ i ∈ s,
      (V * Vᴴ) * (basisEmbedding (A := A) k * Pμ i * (basisEmbedding (A := A) k)ᴴ) * (V * Vᴴ) =
      (V * Pν i * Vᴴ) * (basisEmbedding (A := A) k * Pμ i * (basisEmbedding (A := A) k)ᴴ) *
        (V * Pν i * Vᴴ))
    (hreverse_sector : ∀ i ∈ s,
      (basisEmbedding (A := A) k)ᴴ * (V * Pν i * Vᴴ) * basisEmbedding (A := A) k =
      (basisEmbedding (A := A) k)ᴴ *
        ((basisEmbedding (A := A) k * Pμ i * (basisEmbedding (A := A) k)ᴴ) *
          (V * Pν i * Vᴴ) * (basisEmbedding (A := A) k * Pμ i * (basisEmbedding (A := A) k)ᴴ)) *
        basisEmbedding (A := A) k) :
    BlockRealization s m n pμ pν e ((Fintype.card A : ℝ) / (Fintype.card C : ℝ)) A C :=
  ofWeightBlocks s m n pμ pν e Pμ Pν V hV k
    (Fintype.card A : ℝ) (Fintype.card C : ℝ)
    (by exact_mod_cast (Fintype.card_pos : 0 < Fintype.card A))
    (by exact_mod_cast (Fintype.card_pos : 0 < Fintype.card C))
    (CartanBalance.balance_of_irreducible UA UB UC hUA hUB hUC V hV hintertwine)
    hpμ hpν hPμ hPν htrμ htrν hnormμ hnormν hclose hforward_sector hreverse_sector

end FreeEntropy.CartanCloning
