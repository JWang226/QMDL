/-
Copyright (c) 2026 Free Entropy formalization contributors.
See LICENSE and NOTICE in the repository root for license and attribution.
-/

import FreeEntropy.CartanTraceCloning
import FreeEntropy.CasimirDecomposition

/-!
# Cartan cloning from actual Lie generators and weight decompositions

This adapter derives the local operator gap, exact compressed Casimir,
and retained-branch sector identities from matrix representation data.
Existence of the highest-weight decomposition remains explicit.
-/

noncomputable section
open scoped BigOperators Matrix ComplexOrder MatrixOrder Kronecker
open Matrix

namespace FreeEntropy.CartanLieCloning
open LieMatrixCasimir CasimirWeights WeightSectors CartanChannel
open OrbitMemory CloningMatrices

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySimpa false

variable {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]

theorem weightDiagonal_mul_projector {I : Type*} (w : A → I → ℝ)
    (lam : I → ℝ) (i : I) :
    weightDiagonal w i * weightProjector w lam = lam i • weightProjector w lam := by
  classical
  ext a b
  by_cases hab : a = b
  · subst b
    by_cases ha : w a = lam
    · simp [weightDiagonal, weightProjector, Matrix.diagonal_mul, ha]
    · simp [weightDiagonal, weightProjector, Matrix.diagonal_mul, ha]
  · simp [weightDiagonal, weightProjector, Matrix.diagonal_mul, Matrix.diagonal_apply, hab]

theorem basis_projector (k : B) : IsStarProjection (Matrix.single k k (1 : ℂ)) := by
  refine ⟨?_, ?_⟩
  · change Matrix.single k k (1 : ℂ) * Matrix.single k k 1 = Matrix.single k k 1
    simpa using Matrix.single_mul_single_same (1 : ℂ) k k k 1
  · change (Matrix.single k k (1 : ℂ))ᴴ = _
    simp

theorem basisEmbedding_sandwich (k : B) (P : Matrix A A ℂ) :
    basisEmbedding k * P * (basisEmbedding k)ᴴ = P ⊗ₖ Matrix.single k k 1 := by
  ext ⟨a,b⟩ ⟨c,e⟩
  by_cases hb : b = k <;> by_cases he : e = k <;>
    simp_all [basisEmbedding, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Matrix.one_apply, Matrix.kronecker_apply, Matrix.single_apply, apply_ite,
      eq_comm]

theorem diagonal_mul_basis_projector {I : Type*} (w : B → I → ℝ) (k : B) (i : I) :
    weightDiagonal w i * Matrix.single k k 1 = w k i • Matrix.single k k 1 := by
  ext a b
  by_cases hb : b = k
  · subst b
    by_cases ha : a = k
    · subst a
      simp [weightDiagonal, Matrix.diagonal_mul, Matrix.single_apply]
    · simp [weightDiagonal, Matrix.diagonal_mul, Matrix.single_apply, ha, Ne.symm ha]
  · simp [weightDiagonal, Matrix.diagonal_mul, Matrix.single_apply, hb, Ne.symm hb]

theorem mul_basis_projector_eq_zero (M : Matrix B B ℂ) (k : B)
    (h : ∀ b, M b k = 0) : M * Matrix.single k k 1 = 0 := by
  ext a b
  by_cases hb : b = k
  · subst b
    simp [Matrix.mul_single_apply_same, h]
  · simp [Matrix.mul_single_apply_of_ne, hb]

/-- A cyclic highest-weight matrix representation with a simultaneous
weight basis. The root assignments describe actual basis weights. -/
structure CyclicWeightModel (d : ℕ) (H : Type*) [Fintype H] [DecidableEq H] where
  generators : Generators d H
  row : Fin d → ℝ
  weight : H → Fin d → ℝ
  highest : Matrix H Unit ℂ
  diagonal : ∀ j, generators.E j j = weightDiagonal weight j
  highest_weight : ∀ j, generators.E j j * highest = row j • highest
  highest_raise : ∀ i j, i < j → generators.E i j * highest = 0
  cyclic : generators.cyclicSpan highest = ⊤
  dominant : ∀ j, row (right j) ≤ row (left j)
  weightCoeff : H → Fin (d - 1) → ℕ
  weight_cone : ∀ h, row - weight h = offset (weightCoeff h)

theorem CyclicWeightModel.casimir_scalar {d : ℕ} (M : CyclicWeightModel d A) :
    M.generators.casimir = casimir M.row • (1 : Matrix A A ℂ) :=
  M.generators.casimir_eq_scalar_of_cyclic M.highest M.row M.highest_weight
    M.highest_raise M.cyclic

/-- A cyclic highest vector in a nonzero representation has a nonzero
coordinate, so the chosen joint-weight basis contains the highest weight. -/
theorem CyclicWeightModel.exists_highest_basis {d : ℕ} [Nonempty A]
    (M : CyclicWeightModel d A) : ∃ k, M.weight k = M.row := by
  classical
  have hn : M.highest ≠ 0 := by
    intro hz
    have hc := M.cyclic
    have hbot : M.generators.cyclicSpan M.highest = ⊥ := by
      simp [Generators.cyclicSpan, hz]
    rw [hbot] at hc
    exact bot_ne_top hc
  have hx : ∃ k, M.highest k () ≠ 0 := by
    by_contra h
    push_neg at h
    apply hn
    ext k u
    cases u
    exact h k
  obtain ⟨k, hk⟩ := hx
  refine ⟨k, ?_⟩
  funext j
  have he := congrArg (fun X : Matrix A Unit ℂ => X k ()) (M.highest_weight j)
  rw [M.diagonal j] at he
  simp only [weightDiagonal, Matrix.diagonal_mul, Matrix.smul_apply,
    Algebra.smul_def] at he
  exact Complex.ofReal_injective (mul_right_cancel₀ hk he)

/-- A definite auxiliary highest basis vector, whose existence is proved. -/
def CyclicWeightModel.highestBasis {d : ℕ} [Nonempty A] (M : CyclicWeightModel d A) : A :=
  Classical.choose M.exists_highest_basis

theorem CyclicWeightModel.highestBasis_weight {d : ℕ} [Nonempty A]
    (M : CyclicWeightModel d A) : M.weight M.highestBasis = M.row :=
  Classical.choose_spec M.exists_highest_basis

/-- A nonzero matrix entry of a Lie generator changes its joint weight by
the corresponding actual root; this follows directly from commutators. -/
theorem generator_weight_shift {d : ℕ} (R : Generators d A) (w : A → Fin d → ℝ)
    (hdiag : ∀ l, R.E l l = weightDiagonal w l)
    (i j : Fin d) (hij : i ≠ j) (a b : A) (hnz : R.E i j a b ≠ 0) :
    ∀ l, w a l - w b l = (if l = i then 1 else 0) - (if l = j then 1 else 0) := by
  intro l
  have he := congrArg (fun X : Matrix A A ℂ => X a b) (R.commutator l l i j)
  rw [hdiag l] at he
  simp only [Matrix.sub_apply, weightDiagonal, Matrix.diagonal_mul, Matrix.mul_diagonal] at he
  apply Complex.ofReal_injective
  apply mul_right_cancel₀ hnz
  by_cases hli : l = i
  · subst l
    simp [hij, Ne.symm hij, Complex.ofReal_sub] at he ⊢
    linear_combination he
  · by_cases hlj : l = j
    · subst l
      simp [hij, Ne.symm hij, Complex.ofReal_sub] at he ⊢
      linear_combination he
    · simp only [hli, hlj, Ne.symm hlj, if_false, Complex.ofReal_sub,
        Matrix.zero_apply, zero_sub, sub_zero, Complex.ofReal_zero, neg_zero, zero_mul] at he ⊢
      linear_combination he

/-- Every basis vector at the highest weight is annihilated by all
raising generators. A nonzero raised component would require a negative
simple-root coefficient, contradicting the actual weight-cone assignment. -/
theorem CyclicWeightModel.highest_basis_raise {d : ℕ} (M : CyclicWeightModel d A)
    (k : A) (hk : M.weight k = M.row) :
    ∀ i j, i < j → ∀ a, M.generators.E i j a k = 0 := by
  intro i j hij a
  by_contra hnz
  have hw := generator_weight_shift M.generators M.weight M.diagonal i j (ne_of_lt hij) a k hnz
  let r : Fin (d - 1) := ⟨i.val, by have := j.isLt; have := hij; omega⟩
  have hc (l : Fin d) : offset (M.weightCoeff a) l =
      (if l = j then 1 else 0) - (if l = i then 1 else 0) := by
    have he := congrFun (M.weight_cone a) l
    have hs := hw l
    rw [hk] at hs
    simp only [Pi.sub_apply] at he
    linarith
  have hp := CasimirDecomposition.prefix_offset (M.weightCoeff a) r
  simp_rw [hc] at hp
  rw [Finset.sum_sub_distrib] at hp
  simp only [Finset.sum_ite_eq', Finset.mem_filter, Finset.mem_univ, true_and, r] at hp
  have hijv : i.val < j.val := hij
  simp only [show ¬j.val ≤ i.val by omega, if_false, le_refl, if_true] at hp
  have hn : (0 : ℝ) ≤ M.weightCoeff a r := Nat.cast_nonneg _
  linarith

/-- Actual complete constituent embeddings of a tensor representation.
No scalar Casimir action or spectral inequality is part of this data. -/
structure TensorDecomposition {d : ℕ} (M : CyclicWeightModel d A)
    (N : CyclicWeightModel d B) (κ : Type*) [Fintype κ] [DecidableEq κ]
    (T : κ → Type*) [∀ i, Fintype (T i)] [∀ i, DecidableEq (T i)] where
  constituent : ∀ i, CyclicWeightModel d (T i)
  embedding : ∀ i, Matrix (A × B) (T i) ℂ
  isometry : ∀ i, (embedding i)ᴴ * embedding i = 1
  resolution : ∑ i, embedding i * (embedding i)ᴴ = 1
  intertwines : ∀ i a b, (M.generators.tensor N.generators).E a b * embedding i =
    embedding i * (constituent i).generators.E a b
  top : κ
  topWeight : (constituent top).row = M.row + N.row
  uniqueTop : ∀ i, (constituent i).row = M.row + N.row → i = top
  rootCoeff : κ → Fin (d - 1) → ℕ
  highestCone : ∀ i, M.row + N.row - (constituent i).row = offset (rootCoeff i)

variable {d : ℕ} {κ : Type*} [Fintype κ] [DecidableEq κ]
  {T : κ → Type*} [∀ i, Fintype (T i)] [∀ i, DecidableEq (T i)]

theorem TensorDecomposition.local_gap (M : CyclicWeightModel d A)
    (N : CyclicWeightModel d B) (W : TensorDecomposition M N κ T)
    (delta : Fin (d - 1) → ℕ) (g : ℝ) (hg : 0 ≤ g)
    (hgap : ∀ j, delta j ≠ 0 →
      g ≤ (M.row + N.row) (left j) - (M.row + N.row) (right j)) :
    (g + 2) • (weightProjector (totalWeight M.weight N.weight)
        (M.row + N.row - offset delta) -
      W.embedding W.top * weightProjector (W.constituent W.top).weight
        (M.row + N.row - offset delta) * (W.embedding W.top)ᴴ) ≤
      casimir (M.row + N.row) • (1 : Matrix (A × B) (A × B) ℂ) -
        (M.generators.tensor N.generators).casimir := by
  apply CasimirDecomposition.local_gap_of_cyclic_weight_decomposition
    (M.generators.tensor N.generators) (fun i => (W.constituent i).generators)
    W.embedding (totalWeight M.weight N.weight) (fun i => (W.constituent i).weight)
    (fun i => (W.constituent i).highest) (fun i => (W.constituent i).row)
    (M.row + N.row) (M.row + N.row - offset delta) W.rootCoeff
    (fun i => (W.constituent i).weightCoeff) delta W.top g hg
    W.resolution W.intertwines
  · intro j
    simp only [Generators.tensor, M.diagonal, N.diagonal, totalWeight_diagonal]
  · exact fun i => (W.constituent i).diagonal
  · exact fun i => (W.constituent i).highest_weight
  · exact fun i => (W.constituent i).highest_raise
  · exact fun i => (W.constituent i).cyclic
  · exact W.topWeight
  · exact W.uniqueTop
  · exact W.highestCone
  · exact fun i => (W.constituent i).weight_cone
  · abel
  · intro j
    exact add_le_add (M.dominant j) (N.dominant j)
  · exact fun i => (W.constituent i).dominant
  · exact hgap

/-- The retained auxiliary highest-weight line has exactly the compressed
Casimir deficit used by the cloning estimate. -/
theorem tensor_weight_deficit (M : CyclicWeightModel d A) (N : CyclicWeightModel d B)
    (k : B) (hk : N.weight k = N.row)
    (delta : Fin (d - 1) → ℕ) :
    let Q := basisEmbedding (A := A) k * weightProjector M.weight (M.row - offset delta) *
      (basisEmbedding (A := A) k)ᴴ
    Q * (casimir (M.row + N.row) • (1 : Matrix (A × B) (A × B) ℂ) -
      (M.generators.tensor N.generators).casimir) * Q =
        (2 * dot (offset delta) N.row) • Q := by
  dsimp only
  rw [basisEmbedding_sandwich]
  apply M.generators.tensor_casimir_deficit N.generators
    (weightProjector M.weight (M.row - offset delta)) (Matrix.single k k 1)
    (weightProjector_isStarProjection _ _) (basis_projector k) M.row N.row (offset delta)
  · rw [M.casimir_scalar, Matrix.smul_mul, Matrix.one_mul]
  · intro j
    rw [M.diagonal]
    exact weightDiagonal_mul_projector M.weight (M.row - offset delta) j
  · intro j
    rw [N.diagonal, diagonal_mul_basis_projector, hk]
  · intro i j hij
    exact mul_basis_projector_eq_zero _ k (N.highest_basis_raise k hk i j hij)

def weightMultiplicity {H : Type*} [Fintype H] (w : H → Fin d → ℝ)
    (lam : Fin d → ℝ) : ℕ := by
  classical
  exact (Finset.univ.filter (fun h => w h = lam)).card

theorem trace_weightProjector {H : Type*} [Fintype H] [DecidableEq H]
    (w : H → Fin d → ℝ) (lam : Fin d → ℝ) :
    tr (weightProjector w lam) = (weightMultiplicity w lam : ℝ) := by
  classical
  unfold tr
  rw [weightProjector_trace]
  simp only [Complex.natCast_re]
  unfold weightMultiplicity
  congr 1
  congr 1
  ext h
  simp

/-- Actual Cartan channels with the capped cloning coefficient, constructed
from genuine Lie generators and complete highest-weight decomposition data.
The former operator-gap, compressed-Casimir, trace/rank, and branch-sector
hypotheses are all proved internally. The remaining equal shallow counts
are cardinalities of explicit weight fibers. -/
def ofCyclicWeightDecompositionOfIrreducible
    {ι G : Type*} [Group G] [Nonempty A]
    (M : CyclicWeightModel d A) (N : CyclicWeightModel d B)
    (W : TensorDecomposition M N κ T) [Nonempty (T W.top)]
    (UA : G →* Matrix A A ℂ) (UB : G →* Matrix B B ℂ)
    (UC : G →* Matrix (T W.top) (T W.top) ℂ)
    [Representation.IsIrreducible (Twirling.matrixRepresentation UA)]
    (hUA : ∀ u, (UA u)ᴴ * UA u = 1)
    (hUB : ∀ u, (UB u)ᴴ * UB u = 1)
    (hUC : ∀ u, (UC u)ᴴ * UC u = 1)
    (hgroup : ∀ u, (UA u ⊗ₖ UB u) * W.embedding W.top = W.embedding W.top * UC u)
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
  apply CartanTraceCloning.ofCappedCasimirWeightBlocksOfIrreducible
    UA UB UC hUA hUB hUC s (fun i => depth (delta i))
    (fun i => weightMultiplicity M.weight (M.row - offset (delta i)))
    (fun i => weightMultiplicity (W.constituent W.top).weight
      (M.row + N.row - offset (delta i))) pμ pν D g hD Pμ Pν
    (W.embedding W.top) (W.isometry W.top) k hgroup hpμ hpν
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

end FreeEntropy.CartanLieCloning
