/-
Copyright (c) 2026 Free Entropy formalization contributors.
See LICENSE and NOTICE in the repository root for license and attribution.
-/

import FreeEntropy.LieDecomposition
import FreeEntropy.LieWeightModel

/-! A complete actual family of cyclic highest-weight models for every
finite unitary matrix Lie action, with orthogonal intertwining embeddings.
In particular this constructs the constituents of tensor-product models. -/
noncomputable section
open Matrix
open scoped BigOperators
namespace FreeEntropy.LieDecomposition
open LieMatrixCasimir
set_option backward.isDefEq.respectTransparency false
variable {d : ℕ} {H : Type*} [Fintype H] [DecidableEq H]

/-- An actually constructed orthogonal irreducible Lie decomposition. -/
def irreducibleFamily (R : Generators d H) : Finset (Space H) :=
  (exists_complete_orthogonal_family R).choose

theorem irreducibleFamily_spec (R : Generators d H) :
    (∀ K ∈ irreducibleFamily R, IrreducibleSubspace R K) ∧
    (∀ K ∈ irreducibleFamily R, ∀ L ∈ irreducibleFamily R, K ≠ L →
      UnitaryDecomposition.Orthogonal K L) ∧
    (irreducibleFamily R).sup id = ⊤ :=
  (exists_complete_orthogonal_family R).choose_spec

abbrev Index (R : Generators d H) := ↥(irreducibleFamily R)
abbrev Carrier (R : Generators d H) (i : Index R) := Fin (Module.finrank ℂ i.val)

instance (R : Generators d H) (i : Index R) : Nonempty (Carrier R i) :=
  Fin.pos_iff_nonempty.mp (Submodule.one_le_finrank_iff.mpr
    ((irreducibleFamily_spec R).1 i.val i.property).ne_bot)

/-- The true restricted Lie action of a constituent. -/
def constituentGenerators (R : Generators d H) (i : Index R) : Generators d (Carrier R i) :=
  restricted R i.val ((irreducibleFamily_spec R).1 i.val i.property).invariant

def constituentCoordinates (R : Generators d H) (i : Index R) :
    WeightCoordinates (constituentGenerators R i) :=
  (constituentGenerators R i).weightCoordinates
    (restricted_cyclicSpan_eq_top R i.val ((irreducibleFamily_spec R).1 i.val i.property))

/-- A fully proved constituent weight model; its highest vector, dominance,
cyclicity, diagonal basis and root cone are all constructed. -/
def constituentModel (R : Generators d H) (i : Index R) :
    CartanLieCloning.CyclicWeightModel d (Carrier R i) :=
  (constituentCoordinates R i).model

/-- The constituent's isometric embedding after the proved weight-coordinate change. -/
def constituentEmbedding (R : Generators d H) (i : Index R) : Matrix H (Carrier R i) ℂ :=
  UnitaryDecomposition.embedding i.val * (constituentCoordinates R i).unitary

theorem constituentEmbedding_isometry (R : Generators d H) (i : Index R) :
    (constituentEmbedding R i)ᴴ * constituentEmbedding R i = 1 := by
  simp only [constituentEmbedding, Matrix.conjTranspose_mul, Matrix.mul_assoc,
    ← Matrix.mul_assoc (UnitaryDecomposition.embedding i.val)ᴴ
      (UnitaryDecomposition.embedding i.val), UnitaryDecomposition.embedding_isometry,
    Matrix.one_mul, (constituentCoordinates R i).isometry]

theorem constituentEmbedding_orthogonal (R : Generators d H) (i j : Index R) (hij : i ≠ j) :
    (constituentEmbedding R i)ᴴ * constituentEmbedding R j = 0 := by
  have h := UnitaryDecomposition.embedding_orthogonal
    ((irreducibleFamily_spec R).2.1 i.val i.property j.val j.property
      (fun he => hij (Subtype.ext he)))
  simp only [constituentEmbedding, Matrix.conjTranspose_mul, Matrix.mul_assoc,
    ← Matrix.mul_assoc (UnitaryDecomposition.embedding i.val)ᴴ
      (UnitaryDecomposition.embedding j.val), h, Matrix.zero_mul, Matrix.mul_zero]

theorem constituentEmbedding_resolution (R : Generators d H) :
    (∑ i : Index R, constituentEmbedding R i * (constituentEmbedding R i)ᴴ) = 1 := by
  have he (i : Index R) : constituentEmbedding R i * (constituentEmbedding R i)ᴴ =
      UnitaryDecomposition.embedding i.val * (UnitaryDecomposition.embedding i.val)ᴴ := by
    have hW := mul_eq_one_comm.mp (constituentCoordinates R i).isometry
    simp only [constituentEmbedding, Matrix.conjTranspose_mul, Matrix.mul_assoc,
      ← Matrix.mul_assoc (constituentCoordinates R i).unitary
        (constituentCoordinates R i).unitaryᴴ, hW, Matrix.one_mul]
  simp only [he]
  exact UnitaryDecomposition.embedding_resolution (irreducibleFamily R)
    (irreducibleFamily_spec R).2.1 (irreducibleFamily_spec R).2.2

/-- Actual Lie intertwining for every constituent, in its proved weight coordinates. -/
theorem constituentEmbedding_intertwines (R : Generators d H) (i : Index R) (a b : Fin d) :
    R.E a b * constituentEmbedding R i =
      constituentEmbedding R i * (constituentModel R i).generators.E a b := by
  let J := UnitaryDecomposition.embedding i.val
  let W := (constituentCoordinates R i).unitary
  have hW : W * Wᴴ = 1 := mul_eq_one_comm.mp (constituentCoordinates R i).isometry
  have hE : R.E a b * J = J * (constituentGenerators R i).E a b :=
    embedding_intertwines R i.val ((irreducibleFamily_spec R).1 i.val i.property).invariant a b
  change R.E a b * (J * W) = (J * W) * (constituentCoordinates R i).model.generators.E a b
  rw [(constituentCoordinates R i).generators, ← Matrix.mul_assoc, hE]
  change (J * (constituentGenerators R i).E a b) * W =
    (J * W) * (Wᴴ * (constituentGenerators R i).E a b * W)
  simp only [Matrix.mul_assoc, ← Matrix.mul_assoc W Wᴴ, hW, Matrix.one_mul]

end FreeEntropy.LieDecomposition
