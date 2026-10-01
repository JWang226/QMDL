/-
Copyright (c) 2026 Free Entropy formalization contributors.
See LICENSE and NOTICE in the repository root for license and attribution.
-/

import FreeEntropy.TensorConstituentDecomposition
import FreeEntropy.TensorConstituentWeights
import FreeEntropy.TensorTopExistence

/-! The complete tensor constituent data required by the cloning estimates
are constructed from the two actual cyclic highest-weight matrix models. -/
noncomputable section
open Matrix
namespace FreeEntropy.CartanLieCloning
open LieMatrixCasimir LieDecomposition
set_option backward.isDefEq.respectTransparency false
variable {d : ℕ} {A B : Type*} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
  [Nonempty A] [Nonempty B]

/-- A genuine highest constituent exists in the constructed decomposition. -/
theorem constructed_tensor_top_exists (M : CyclicWeightModel d A) (N : CyclicWeightModel d B) :
    ∃ i : LieDecomposition.Index (M.generators.tensor N.generators),
      (constituentModel (M.generators.tensor N.generators) i).row = M.row + N.row :=
  tensor_top_exists M N (constituentModel _) (constituentEmbedding _)
    (constituentEmbedding_resolution _) (constituentEmbedding_intertwines _)

/-- Complete actual tensor decomposition. Top existence, multiplicity one,
and the highest-root cone are proved, not supplied as structural premises. -/
def constructedTensorDecomposition (M : CyclicWeightModel d A) (N : CyclicWeightModel d B) :
    TensorDecomposition M N (LieDecomposition.Index (M.generators.tensor N.generators))
      (LieDecomposition.Carrier (M.generators.tensor N.generators)) where
  constituent := constituentModel _
  embedding := constituentEmbedding _
  isometry := constituentEmbedding_isometry _
  resolution := constituentEmbedding_resolution _
  intertwines := constituentEmbedding_intertwines _
  top := (constructed_tensor_top_exists M N).choose
  topWeight := (constructed_tensor_top_exists M N).choose_spec
  uniqueTop i hi := by
    by_contra hn
    exact tensor_top_not_orthogonal M N
      (constituentModel _ i)
      (constituentModel _ (constructed_tensor_top_exists M N).choose)
      (constituentEmbedding _ i)
      (constituentEmbedding _ (constructed_tensor_top_exists M N).choose)
      (constituentEmbedding_isometry _ i)
      (constituentEmbedding_isometry _ _)
      (constituentEmbedding_intertwines _ i)
      (constituentEmbedding_intertwines _ _) hi
      (constructed_tensor_top_exists M N).choose_spec
      (constituentEmbedding_orthogonal _ i _ hn)
  rootCoeff i := (tensor_constituent_highest_cone M N (constituentModel _ i)
    (constituentEmbedding _ i) (constituentEmbedding_isometry _ i)
    (constituentEmbedding_intertwines _ i)).choose
  highestCone i := (tensor_constituent_highest_cone M N (constituentModel _ i)
    (constituentEmbedding _ i) (constituentEmbedding_isometry _ i)
    (constituentEmbedding_intertwines _ i)).choose_spec

end FreeEntropy.CartanLieCloning
