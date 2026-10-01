/-
Copyright (c) 2026 Free Entropy formalization contributors.
See LICENSE and NOTICE in the repository root for license and attribution.
-/

import FreeEntropy.ConstructedTensorDecomposition
import FreeEntropy.LieCartanBalance
import FreeEntropy.CartanTraceCloningBalance

/-! Actual cloning trace blocks from Lie highest-weight models, without
assumed group representations, group irreducibility, or channel balance.
The tensor decomposition has a fully constructed default instance. -/
noncomputable section
open scoped BigOperators Matrix ComplexOrder MatrixOrder Kronecker
open Matrix
namespace FreeEntropy.CartanLieCloning
open LieMatrixCasimir CasimirWeights WeightSectors CartanChannel
open OrbitMemory CloningMatrices
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
variable {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
variable {d : ℕ} {κ : Type*} [Fintype κ] [DecidableEq κ]
  {T : κ → Type*} [∀ i, Fintype (T i)] [∀ i, DecidableEq (T i)]

def ofCyclicWeightDecomposition
    {ι : Type*} [Nonempty A]
    (M : CyclicWeightModel d A) (N : CyclicWeightModel d B)
    (W : TensorDecomposition M N κ T) [Nonempty (T W.top)]
    (k : B) (hk : N.weight k = N.row)
    (s : Finset ι) (delta : ι → Fin (d - 1) → ℕ) (pμ pν : ι → ℝ)
    (D g : ℕ) (hD : 1 ≤ D) (hDnorm : l1 N.row ≤ (D : ℝ))
    (hpμ : ∀ i ∈ s, 0 ≤ pμ i) (hpν : ∀ i ∈ s, 0 ≤ pν i)
    (hnormμ : (mixture s pμ
      (fun i => weightProjector M.weight (M.row - offset (delta i)))).trace = 1)
    (hnormν : (mixture s pν (fun i => weightProjector (W.constituent W.top).weight
      (M.row + N.row - offset (delta i)))).trace = 1)
    (hshallow : ∀ i ∈ s, depth (delta i) ≤ g →
      weightMultiplicity M.weight (M.row - offset (delta i)) =
      weightMultiplicity (W.constituent W.top).weight (M.row + N.row - offset (delta i)))
    (hgap : ∀ i ∈ s, depth (delta i) ≤ g → ∀ j, delta i j ≠ 0 →
      (g : ℝ) ≤ (M.row + N.row) (left j) - (M.row + N.row) (right j)) :
    TraceCloning.TraceBlockRealization s
      (fun i => weightMultiplicity M.weight (M.row - offset (delta i)))
      (fun i => weightMultiplicity (W.constituent W.top).weight
        (M.row + N.row - offset (delta i)))
      pμ pν (fun i => min 1 (2 * (depth (delta i) : ℝ) * (D : ℝ) / ((g : ℝ) + 2)))
      ((Fintype.card A : ℝ) / (Fintype.card (T W.top) : ℝ)) A (T W.top) := by
  classical
  let Pμ := fun i => weightProjector M.weight (M.row - offset (delta i))
  let Pν := fun i => weightProjector (W.constituent W.top).weight
    (M.row + N.row - offset (delta i))
  let Q := fun i => basisEmbedding (A := A) k * Pμ i * (basisEmbedding (A := A) k)ᴴ
  let S := fun i => weightProjector (totalWeight M.weight N.weight)
    (M.row + N.row - offset (delta i))
  let K := casimir (M.row + N.row) • (1 : Matrix (A × B) (A × B) ℂ) -
    (M.generators.tensor N.generators).casimir
  have hcartan : ∀ j,
      (weightDiagonal M.weight j ⊗ₖ (1 : Matrix B B ℂ) +
        (1 : Matrix A A ℂ) ⊗ₖ weightDiagonal N.weight j) * W.embedding W.top =
          W.embedding W.top * weightDiagonal (W.constituent W.top).weight j := by
    intro j
    simpa only [Generators.tensor, M.diagonal, N.diagonal,
      (W.constituent W.top).diagonal] using W.intertwines W.top j j
  have hsectors (i : ι) :
      (W.embedding W.top * (W.embedding W.top)ᴴ) * Q i *
        (W.embedding W.top * (W.embedding W.top)ᴴ) =
      (W.embedding W.top * Pν i * (W.embedding W.top)ᴴ) * Q i *
        (W.embedding W.top * Pν i * (W.embedding W.top)ᴴ) ∧
      (basisEmbedding (A := A) k)ᴴ *
        (W.embedding W.top * Pν i * (W.embedding W.top)ᴴ) * basisEmbedding (A := A) k =
      (basisEmbedding (A := A) k)ᴴ *
        (Q i * (W.embedding W.top * Pν i * (W.embedding W.top)ᴴ) * Q i) *
          basisEmbedding (A := A) k ∧ Q i * S i * Q i = Q i := by
    have hshift : (M.row - offset (delta i)) + N.weight k =
        M.row + N.row - offset (delta i) := by rw [hk]; abel
    simpa only [hshift, Q, Pμ, Pν, S] using
      cloning_weight_sector_identities M.weight N.weight (W.constituent W.top).weight
        (W.embedding W.top) hcartan k (M.row - offset (delta i))
  apply CartanTraceCloning.ofCappedCasimirWeightBlocks
    s (fun i => depth (delta i))
    (fun i => weightMultiplicity M.weight (M.row - offset (delta i)))
    (fun i => weightMultiplicity (W.constituent W.top).weight
      (M.row + N.row - offset (delta i))) pμ pν D g hD Pμ Pν
    (W.embedding W.top) (W.isometry W.top) k
    (CartanBalance.balance_of_cyclic_weight M N (W.constituent W.top)
      (W.embedding W.top) (W.isometry W.top) (W.intertwines W.top)) hpμ hpν
    (fun i _ => weightProjector_isStarProjection _ _)
    (fun i _ => weightProjector_isStarProjection _ _)
    (fun i _ => trace_weightProjector _ _) (fun i _ => trace_weightProjector _ _)
    hnormμ hnormν (fun _ => K) S (fun i => 2 * dot (offset (delta i)) N.row)
    hshallow
  · intro i hi hsmall
    exact W.local_gap M N (delta i) (g : ℝ) (Nat.cast_nonneg _) (hgap i hi hsmall)
  · intro i _ _
    exact (hsectors i).2.2
  · intro i _ _
    exact (tensor_weight_deficit M N k hk (delta i)).le
  · intro i _ _
    have h := (offset_dot_bounds (delta i) N.row N.dominant).2
    have hd : 0 ≤ (depth (delta i) : ℝ) := Nat.cast_nonneg _
    have hdot : dot N.row (offset (delta i)) = dot (offset (delta i)) N.row := by
      unfold dot
      apply Finset.sum_congr rfl
      intro j _
      ring
    rw [hdot] at h
    nlinarith
  · intro i _
    exact (hsectors i).1
  · intro i _
    exact (hsectors i).2.1

/-- The actual top carrier in the constructed tensor decomposition. -/
abbrev ConstructedTopSpace [Nonempty A] [Nonempty B]
    (M : CyclicWeightModel d A) (N : CyclicWeightModel d B) :=
  LieDecomposition.Carrier (M.generators.tensor N.generators)
    (constructedTensorDecomposition M N).top

/-- The actual highest-sum model selected by the proved top existence. -/
abbrev constructedTopModel [Nonempty A] [Nonempty B]
    (M : CyclicWeightModel d A) (N : CyclicWeightModel d B) :
    CyclicWeightModel d (ConstructedTopSpace M N) :=
  (constructedTensorDecomposition M N).constituent (constructedTensorDecomposition M N).top

/-- The decomposition, top constituent, root cones, local Casimir gap and
channel normalization are all constructed here. The remaining inputs are
scalar state coefficients and their shallow weight-multiplicity equality. -/
def ofConstructedCyclicWeights
    {ι : Type*} [Nonempty A] [Nonempty B]
    (M : CyclicWeightModel d A) (N : CyclicWeightModel d B)
    (k : B) (hk : N.weight k = N.row)
    (s : Finset ι) (delta : ι → Fin (d - 1) → ℕ) (pμ pν : ι → ℝ)
    (D g : ℕ) (hD : 1 ≤ D) (hDnorm : l1 N.row ≤ (D : ℝ))
    (hpμ : ∀ i ∈ s, 0 ≤ pμ i) (hpν : ∀ i ∈ s, 0 ≤ pν i)
    (hnormμ : (mixture s pμ
      (fun i => weightProjector M.weight (M.row - offset (delta i)))).trace = 1)
    (hnormν : (mixture s pν (fun i => weightProjector (constructedTopModel M N).weight
      (M.row + N.row - offset (delta i)))).trace = 1)
    (hshallow : ∀ i ∈ s, depth (delta i) ≤ g →
      weightMultiplicity M.weight (M.row - offset (delta i)) =
      weightMultiplicity (constructedTopModel M N).weight (M.row + N.row - offset (delta i)))
    (hgap : ∀ i ∈ s, depth (delta i) ≤ g → ∀ j, delta i j ≠ 0 →
      (g : ℝ) ≤ (M.row + N.row) (left j) - (M.row + N.row) (right j)) :
    TraceCloning.TraceBlockRealization s
      (fun i => weightMultiplicity M.weight (M.row - offset (delta i)))
      (fun i => weightMultiplicity (constructedTopModel M N).weight
        (M.row + N.row - offset (delta i)))
      pμ pν (fun i => min 1 (2 * (depth (delta i) : ℝ) * (D : ℝ) / ((g : ℝ) + 2)))
      ((Fintype.card A : ℝ) / (Fintype.card (ConstructedTopSpace M N) : ℝ)) A (ConstructedTopSpace M N) :=
  ofCyclicWeightDecomposition M N (constructedTensorDecomposition M N)
    k hk s delta pμ pν D g hD hDnorm hpμ hpν hnormμ hnormν hshallow hgap

end FreeEntropy.CartanLieCloning
