/-
Copyright (c) 2026 Free Entropy formalization contributors.
See LICENSE and NOTICE in the repository root for license and attribution.
-/

import FreeEntropy.UnitaryDecompositionMatrices

/-! An actual complete orthogonal irreducible decomposition constructed from
an arbitrary finite-dimensional unitary group representation. -/

noncomputable section
open Matrix

namespace FreeEntropy.UnitaryDecomposition

variable {G H : Type*} [Group G] [Fintype H] [DecidableEq H]

/-- The stored subspaces are genuine irreducible invariant subspaces of the
given representation; their existence is proved below. -/
structure Decomposition (U : G →* Matrix H H ℂ) where
  subspaces : Finset (Subspace H)
  irreducibleSubspace : ∀ K ∈ subspaces, IrreducibleSubspace (euclideanRepresentation U) K
  pairwiseOrthogonal : ∀ K ∈ subspaces, ∀ L ∈ subspaces, K ≠ L → Orthogonal K L
  span_top : subspaces.sup id = ⊤

/-- Actual construction, by finite-dimensional orthogonal induction. -/
def decomposition (U : G →* Matrix H H ℂ) (hU : ∀ g, (U g)ᴴ * U g = 1) :
    Decomposition U := by
  classical
  let hex := exists_complete_orthogonal_family (euclideanRepresentation U)
    (euclideanRepresentation_adjoint U hU)
  exact ⟨Classical.choose hex, (Classical.choose_spec hex).1,
    (Classical.choose_spec hex).2.1, (Classical.choose_spec hex).2.2⟩

namespace Decomposition
variable {U : G →* Matrix H H ℂ} (D : Decomposition U)

abbrev Index := D.subspaces

def dimension (i : D.Index) : ℕ := Module.finrank ℂ i.val

def embedding (i : D.Index) : Matrix H (Fin (D.dimension i)) ℂ :=
  UnitaryDecomposition.embedding i.val

def representation (i : D.Index) : G →* Matrix (Fin (D.dimension i)) (Fin (D.dimension i)) ℂ :=
  restrictedMatrix U i.val (D.irreducibleSubspace i.val i.property).invariant

theorem dimension_pos (i : D.Index) : 0 < D.dimension i :=
  Submodule.one_le_finrank_iff.mpr (D.irreducibleSubspace i.val i.property).ne_bot

theorem isometry (i : D.Index) : (D.embedding i)ᴴ * D.embedding i = 1 :=
  embedding_isometry i.val

theorem orthogonal (i j : D.Index) (h : i ≠ j) :
    (D.embedding i)ᴴ * D.embedding j = 0 :=
  embedding_orthogonal (D.pairwiseOrthogonal i.val i.property j.val j.property
    (fun e => h (Subtype.ext e)))

theorem resolution : (∑ i : D.Index, D.embedding i * (D.embedding i)ᴴ) = 1 :=
  embedding_resolution D.subspaces D.pairwiseOrthogonal D.span_top

theorem intertwines (i : D.Index) (g : G) :
    U g * D.embedding i = D.embedding i * D.representation i g :=
  embedding_intertwines U i.val (D.irreducibleSubspace i.val i.property).invariant g

theorem irreducible (i : D.Index) :
    Representation.IsIrreducible (Twirling.matrixRepresentation (D.representation i)) :=
  restrictedMatrix_irreducible U i.val _
    (D.irreducibleSubspace i.val i.property).isIrreducible

theorem unitary (hU : ∀ g, (U g)ᴴ * U g = 1) (i : D.Index) (g : G) :
    (D.representation i g)ᴴ * D.representation i g = 1 :=
  restrictedMatrix_unitary U hU i.val _ g

open scoped Matrix.Norms.Elementwise in
 theorem continuous [TopologicalSpace G] (hU : Continuous U) (i : D.Index) :
    Continuous (D.representation i) :=
  restrictedMatrix_continuous U hU i.val _

end Decomposition
end FreeEntropy.UnitaryDecomposition
