/-
Copyright (c) 2026 Free Entropy formalization contributors.
See LICENSE and NOTICE in the repository root for license and attribution.
-/

import FreeEntropy.ConstructedLieCloning
import FreeEntropy.SignedCartan

/-! The constructed Cartan block geometry on any specified target model
with the sum highest weight. An actual highest-weight unitary identifies
the chosen decomposition's top carrier with that target. -/
noncomputable section
open Matrix
open scoped BigOperators Matrix ComplexOrder MatrixOrder Kronecker
namespace FreeEntropy.CartanLieCloning
open LieMatrixCasimir CasimirWeights WeightSectors CartanChannel
open OrbitMemory CloningMatrices
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
variable {d : ℕ} {A B C : Type*} [Fintype A] [DecidableEq A]
  [Fintype B] [DecidableEq B] [Fintype C] [DecidableEq C]
  [Nonempty A] [Nonempty B] [Nonempty C]

theorem exists_specifiedTopUnitary (M : CyclicWeightModel d A)
    (N : CyclicWeightModel d B) (S : CyclicWeightModel d C)
    (hrow : S.row = M.row + N.row) :
    ∃ W : Matrix C (ConstructedTopSpace M N) ℂ, Wᴴ * W = 1 ∧ W * Wᴴ = 1 ∧
      ∀ i j, W * (constructedTopModel M N).generators.E i j = S.generators.E i j * W := by
  let T := constructedTopModel M N
  apply LiePBW.exists_highest_unitary T.generators S.generators (fun i => (S.row i : ℂ))
    T.highestVector S.highestVector T.highestVector_ne_zero S.highestVector_ne_zero
  · intro i
    rw [show S.row = T.row from hrow.trans (constructedTensorDecomposition M N).topWeight.symm]
    exact T.vector_weight i
  · exact S.vector_weight
  · exact T.vector_raise
  · exact S.vector_raise
  · exact T.vector_cyclic
  · exact S.vector_cyclic

def specifiedTopUnitary (M : CyclicWeightModel d A) (N : CyclicWeightModel d B)
    (S : CyclicWeightModel d C) (hrow : S.row = M.row + N.row) : Matrix C (ConstructedTopSpace M N) ℂ :=
  (exists_specifiedTopUnitary M N S hrow).choose

theorem specifiedTopUnitary_spec (M : CyclicWeightModel d A) (N : CyclicWeightModel d B)
    (S : CyclicWeightModel d C) (hrow : S.row = M.row + N.row) :
    (specifiedTopUnitary M N S hrow)ᴴ * specifiedTopUnitary M N S hrow = 1 ∧
      specifiedTopUnitary M N S hrow * (specifiedTopUnitary M N S hrow)ᴴ = 1 ∧
      ∀ i j, specifiedTopUnitary M N S hrow * (constructedTopModel M N).generators.E i j =
        S.generators.E i j * specifiedTopUnitary M N S hrow :=
  (exists_specifiedTopUnitary M N S hrow).choose_spec

def specifiedCartanEmbedding (M : CyclicWeightModel d A) (N : CyclicWeightModel d B)
    (S : CyclicWeightModel d C) (hrow : S.row = M.row + N.row) : Matrix (A × B) C ℂ :=
  (constructedTensorDecomposition M N).embedding (constructedTensorDecomposition M N).top *
    (specifiedTopUnitary M N S hrow)ᴴ

theorem specifiedCartanEmbedding_isometry (M : CyclicWeightModel d A) (N : CyclicWeightModel d B)
    (S : CyclicWeightModel d C) (hrow : S.row = M.row + N.row) :
    (specifiedCartanEmbedding M N S hrow)ᴴ * specifiedCartanEmbedding M N S hrow = 1 := by
  let D := constructedTensorDecomposition M N
  let U := specifiedTopUnitary M N S hrow
  have hW := specifiedTopUnitary_spec M N S hrow
  change (D.embedding D.top * Uᴴ)ᴴ * (D.embedding D.top * Uᴴ) = 1
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc,
    ← Matrix.mul_assoc (D.embedding D.top)ᴴ (D.embedding D.top), D.isometry, Matrix.one_mul]
  exact hW.2.1

theorem specifiedTopUnitary_adjoint_intertwines (M : CyclicWeightModel d A) (N : CyclicWeightModel d B)
    (S : CyclicWeightModel d C) (hrow : S.row = M.row + N.row) (i j : Fin d) :
    (constructedTopModel M N).generators.E i j * (specifiedTopUnitary M N S hrow)ᴴ =
      (specifiedTopUnitary M N S hrow)ᴴ * S.generators.E i j := by
  simpa only [Matrix.conjTranspose_mul, Generators.adjoint] using
    congrArg Matrix.conjTranspose ((specifiedTopUnitary_spec M N S hrow).2.2 j i)

theorem specifiedCartanEmbedding_intertwines (M : CyclicWeightModel d A) (N : CyclicWeightModel d B)
    (S : CyclicWeightModel d C) (hrow : S.row = M.row + N.row) (i j : Fin d) :
    (M.generators.tensor N.generators).E i j * specifiedCartanEmbedding M N S hrow =
      specifiedCartanEmbedding M N S hrow * S.generators.E i j := by
  let D := constructedTensorDecomposition M N
  simp only [specifiedCartanEmbedding]
  rw [← Matrix.mul_assoc, D.intertwines, Matrix.mul_assoc,
    specifiedTopUnitary_adjoint_intertwines M N S hrow, ← Matrix.mul_assoc]

/-- The specified target has exactly the constructed top weight-sector
projection in the common ambient tensor space. -/
theorem specifiedCartanEmbedding_weight_projection (M : CyclicWeightModel d A) (N : CyclicWeightModel d B)
    (S : CyclicWeightModel d C) (hrow : S.row = M.row + N.row) (wt : Fin d → ℝ) :
    specifiedCartanEmbedding M N S hrow * weightProjector S.weight wt *
        (specifiedCartanEmbedding M N S hrow)ᴴ =
      (constructedTensorDecomposition M N).embedding (constructedTensorDecomposition M N).top *
        weightProjector (constructedTopModel M N).weight wt *
        ((constructedTensorDecomposition M N).embedding (constructedTensorDecomposition M N).top)ᴴ := by
  let U := specifiedTopUnitary M N S hrow
  let D := constructedTensorDecomposition M N
  have hp : weightProjector (constructedTopModel M N).weight wt * Uᴴ = Uᴴ * weightProjector S.weight wt := by
    apply weightProjector_intertwines
    intro i
    simpa only [(constructedTopModel M N).diagonal, S.diagonal] using
      specifiedTopUnitary_adjoint_intertwines M N S hrow i i
  have hU := (specifiedTopUnitary_spec M N S hrow).1
  change (D.embedding D.top * Uᴴ) * weightProjector S.weight wt * (D.embedding D.top * Uᴴ)ᴴ = _
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
    Matrix.mul_assoc (D.embedding D.top), ← hp]
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc Uᴴ U, hU, Matrix.one_mul]

/-- All local Cartan spectral geometry is derived for the specified target. -/
def ofSpecifiedCyclicWeights {ι : Type*}
    (M : CyclicWeightModel d A) (N : CyclicWeightModel d B) (S : CyclicWeightModel d C)
    (hrow : S.row = M.row + N.row)
    (s : Finset ι) (delta : ι → Fin (d - 1) → ℕ) (pμ pν : ι → ℝ)
    (D g : ℕ) (hD : 1 ≤ D) (hDnorm : l1 N.row ≤ (D : ℝ))
    (hpμ : ∀ i ∈ s, 0 ≤ pμ i) (hpν : ∀ i ∈ s, 0 ≤ pν i)
    (hnormμ : (mixture s pμ (fun i => weightProjector M.weight (M.row - offset (delta i)))).trace = 1)
    (hnormν : (mixture s pν (fun i => weightProjector S.weight (M.row + N.row - offset (delta i)))).trace = 1)
    (hshallow : ∀ i ∈ s, depth (delta i) ≤ g →
      weightMultiplicity M.weight (M.row - offset (delta i)) =
      weightMultiplicity S.weight (M.row + N.row - offset (delta i)))
    (hgap : ∀ i ∈ s, depth (delta i) ≤ g → ∀ j, delta i j ≠ 0 →
      (g : ℝ) ≤ (M.row + N.row) (left j) - (M.row + N.row) (right j)) :
    TraceCloning.TraceBlockRealization s
      (fun i => weightMultiplicity M.weight (M.row - offset (delta i)))
      (fun i => weightMultiplicity S.weight (M.row + N.row - offset (delta i)))
      pμ pν (fun i => min 1 (2 * (depth (delta i) : ℝ) * (D : ℝ) / ((g : ℝ) + 2)))
      ((Fintype.card A : ℝ) / (Fintype.card C : ℝ)) A C := by
  classical
  let W := constructedTensorDecomposition M N
  let V := specifiedCartanEmbedding M N S hrow
  let k := N.highestBasis
  have hk : N.weight k = N.row := N.highestBasis_weight
  have hV := specifiedCartanEmbedding_isometry M N S hrow
  have hVE := specifiedCartanEmbedding_intertwines M N S hrow
  let Pμ := fun i => weightProjector M.weight (M.row - offset (delta i))
  let Pν := fun i => weightProjector S.weight (M.row + N.row - offset (delta i))
  let Q := fun i => basisEmbedding (A := A) k * Pμ i * (basisEmbedding (A := A) k)ᴴ
  let Ptot := fun i => weightProjector (totalWeight M.weight N.weight) (M.row + N.row - offset (delta i))
  let K := casimir (M.row + N.row) • (1 : Matrix (A × B) (A × B) ℂ) - (M.generators.tensor N.generators).casimir
  have hcartan : ∀ j,
      (weightDiagonal M.weight j ⊗ₖ (1 : Matrix B B ℂ) +
        (1 : Matrix A A ℂ) ⊗ₖ weightDiagonal N.weight j) * V = V * weightDiagonal S.weight j := by
    intro j
    simpa only [Generators.tensor, M.diagonal, N.diagonal, S.diagonal] using hVE j j
  have hsectors (i : ι) :
      (V * Vᴴ) * Q i * (V * Vᴴ) = (V * Pν i * Vᴴ) * Q i * (V * Pν i * Vᴴ) ∧
      (basisEmbedding (A := A) k)ᴴ * (V * Pν i * Vᴴ) * basisEmbedding (A := A) k =
      (basisEmbedding (A := A) k)ᴴ * (Q i * (V * Pν i * Vᴴ) * Q i) * basisEmbedding (A := A) k ∧
      Q i * Ptot i * Q i = Q i := by
    have hshift : (M.row - offset (delta i)) + N.weight k = M.row + N.row - offset (delta i) := by rw [hk]; abel
    simpa only [hshift, Q, Pμ, Pν, Ptot] using
      cloning_weight_sector_identities M.weight N.weight S.weight V hcartan k (M.row - offset (delta i))
  apply CartanTraceCloning.ofCappedCasimirWeightBlocks s (fun i => depth (delta i))
    (fun i => weightMultiplicity M.weight (M.row - offset (delta i)))
    (fun i => weightMultiplicity S.weight (M.row + N.row - offset (delta i)))
    pμ pν D g hD Pμ Pν V hV k
    (CartanBalance.balance_of_cyclic_weight M N S V hV hVE) hpμ hpν
    (fun _ _ => weightProjector_isStarProjection _ _) (fun _ _ => weightProjector_isStarProjection _ _)
    (fun _ _ => trace_weightProjector _ _) (fun _ _ => trace_weightProjector _ _)
    hnormμ hnormν (fun _ => K) Ptot (fun i => 2 * dot (offset (delta i)) N.row) hshallow
  · intro i hi hsmall
    have h := W.local_gap M N (delta i) (g : ℝ) (Nat.cast_nonneg _) (hgap i hi hsmall)
    change ((g : ℝ) + 2) • (Ptot i - V * Pν i * Vᴴ) ≤ K
    rw [show V * Pν i * Vᴴ = W.embedding W.top * weightProjector (W.constituent W.top).weight
      (M.row + N.row - offset (delta i)) * (W.embedding W.top)ᴴ from
      specifiedCartanEmbedding_weight_projection M N S hrow _]
    exact h
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

end FreeEntropy.CartanLieCloning
