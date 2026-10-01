/-
Copyright (c) 2026 Free Entropy formalization contributors.
See LICENSE and NOTICE in the repository root for license and attribution.
-/

import FreeEntropy.TensorLieCyclicityPhysical
import Mathlib.Analysis.InnerProductSpace.JointEigenspace

/-! Simultaneous orthonormal weight bases are constructed for the actual
physical tensor sectors. Their labels are proved to be natural word contents. -/
noncomputable section
open Matrix
open scoped BigOperators ComplexInnerProductSpace

namespace FreeEntropy.LieMatrixCasimir
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
set_option linter.unusedSectionVars false
variable {d : ℕ} {A : Type*} [Fintype A] [DecidableEq A]

theorem Generators.diagonal_commute (R : Generators d A) (i j : Fin d) :
    R.E i i * R.E j j = R.E j j * R.E i i := by
  apply sub_eq_zero.mp
  rw [R.commutator]
  by_cases h : i = j
  · subst j; simp
  · simp [h, Ne.symm h]

/-- The joint spectral theorem constructs a simultaneous orthonormal basis
for the diagonal generators of any genuine unitary matrix Lie action. -/
theorem Generators.exists_jointBasis (R : Generators d A) :
    ∃ b : OrthonormalBasis A ℂ (EuclideanSpace ℂ A), ∃ χ : A → Fin d → ℂ,
      ∀ a j, R.E j j *ᵥ (b a).ofLp = χ a j • (b a).ofLp := by
  classical
  let T (j : Fin d) := Matrix.toEuclideanLin (R.E j j)
  have hT (j : Fin d) : (T j).IsSymmetric :=
    Matrix.isHermitian_iff_isSymmetric.mp (R.adjoint j j)
  have hc : Pairwise (fun i j => Commute (T i) (T j)) := by
    intro i j _
    apply LinearMap.ext
    intro v
    change Matrix.toEuclideanLin (R.E i i) (Matrix.toEuclideanLin (R.E j j) v) =
      Matrix.toEuclideanLin (R.E j j) (Matrix.toEuclideanLin (R.E i i) v)
    simp only [Matrix.toLpLin_apply, Matrix.mulVec_mulVec,
      R.diagonal_commute i j]
  let V (χ : Fin d → ℂ) : Submodule ℂ (EuclideanSpace ℂ A) :=
    ⨅ j, Module.End.eigenspace (T j) (χ j)
  let Λ := ∀ j : Fin d, Module.End.Eigenvalues (T j)
  let W (χ : Λ) : Submodule ℂ (EuclideanSpace ℂ A) := V (fun j => (χ j).val)
  have hoAll := LinearMap.IsSymmetric.orthogonalFamily_iInf_eigenspaces hT
  let forget : Λ → (Fin d → ℂ) := fun f j => (f j).val
  have hf : Function.Injective forget := by
    intro f g hfg
    funext j
    exact Subtype.ext (congrFun hfg j)
  have ho := hoAll.comp hf
  have hspan : (⨆ χ : Λ, W χ) = ⊤ := by
    apply top_unique
    rw [← LinearMap.IsSymmetric.iSup_iInf_eq_top_of_commute hT hc]
    apply iSup_le
    intro χ
    by_cases hzero : V χ = ⊥
    · change V χ ≤ _
      rw [hzero]
      exact bot_le
    · let f : Λ := fun j => ⟨χ j, fun hz => hzero (eq_bot_iff.mpr
        ((iInf_le (fun k => Module.End.eigenspace (T k) (χ k)) j).trans (le_of_eq hz)))⟩
      exact le_iSup W f
  have hd : DirectSum.IsInternal W := ho.isInternal_iff.mpr (by
    rw [hspan, Submodule.top_orthogonal_eq_bot])
  let b := hd.subordinateOrthonormalBasis (n := Fintype.card A) finrank_euclideanSpace ho
  let e : Fin (Fintype.card A) ≃ A := (Fintype.equivFin A).symm
  let χ : A → Fin d → ℂ := fun a =>
    fun j => (hd.subordinateOrthonormalBasisIndex finrank_euclideanSpace (e.symm a) ho j).val
  refine ⟨b.reindex e, χ, ?_⟩
  intro a j
  have hm := hd.subordinateOrthonormalBasis_subordinate finrank_euclideanSpace (e.symm a) ho
  simp only [W, V, Submodule.mem_iInf] at hm
  have hj := hm j
  rw [Module.End.mem_eigenspace_iff] at hj
  simpa only [OrthonormalBasis.reindex_apply, b, χ, T, Matrix.toLpLin_apply,
    WithLp.ofLp_toLp, WithLp.ofLp_smul] using congrArg WithLp.ofLp hj

end FreeEntropy.LieMatrixCasimir

namespace FreeEntropy.SchurWeyl
open Occupation
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
set_option linter.unusedSectionVars false
variable {d n : ℕ}

/-- A choice of a proved simultaneous orthonormal basis in an actual sector. -/
def sectorJointBasis (i : Sector d n) :
    OrthonormalBasis (SectorSpace d n i) ℂ (EuclideanSpace ℂ (SectorSpace d n i)) :=
  (LieMatrixCasimir.Generators.exists_jointBasis (sectorGenerators i)).choose

def sectorJointEigenvalue (i : Sector d n) : SectorSpace d n i → Fin d → ℂ :=
  (LieMatrixCasimir.Generators.exists_jointBasis (sectorGenerators i)).choose_spec.choose

theorem sectorJointBasis_weight (i : Sector d n) (a : SectorSpace d n i) (j : Fin d) :
    (sectorGenerators i).E j j *ᵥ (sectorJointBasis i a).ofLp =
      sectorJointEigenvalue i a j • (sectorJointBasis i a).ofLp :=
  (LieMatrixCasimir.Generators.exists_jointBasis (sectorGenerators i)).choose_spec.choose_spec a j

/-- Every joint eigenvalue in a physical tensor summand is an actual natural
word content, proved from a nonzero embedded coordinate. -/
theorem sectorJointEigenvalue_is_occupation (i : Sector d n) (a : SectorSpace d n i) :
    ∃ w : Occupation d n, ∀ j, sectorJointEigenvalue i a j = (w.val j : ℂ) := by
  let J := (physicalDecomposition d n).embedding i
  let v := (sectorJointBasis i a).ofLp
  have hv : v ≠ 0 := by
    intro h
    have hb : sectorJointBasis i a = 0 := WithLp.ofLp_injective 2 h
    have hn := (sectorJointBasis i).norm_eq_one a
    rw [hb, norm_zero] at hn
    exact zero_ne_one hn
  have hJv : J *ᵥ v ≠ 0 := by
    intro h
    apply hv
    have hh := congrArg (fun x => Jᴴ *ᵥ x) h
    simpa only [Matrix.mulVec_mulVec, J, (physicalDecomposition d n).isometry,
      Matrix.one_mulVec, Matrix.mulVec_zero] using hh
  obtain ⟨w, hw⟩ : ∃ w, (J *ᵥ v) w ≠ 0 := by
    by_contra hn
    push_neg at hn
    exact hJv (funext hn)
  refine ⟨ofWord w, ?_⟩
  intro j
  have hweight : (TensorPowers.generators d n).E j j *ᵥ (J *ᵥ v) =
      sectorJointEigenvalue i a j • (J *ᵥ v) := by
    rw [Matrix.mulVec_mulVec,
      restrictedGenerators_intertwines ((physicalDecomposition d n).representation i)
        J ((physicalDecomposition d n).isometry i) ((physicalDecomposition d n).intertwines i),
      ← Matrix.mulVec_mulVec]
    change J *ᵥ ((sectorGenerators i).E j j *ᵥ (sectorJointBasis i a).ofLp) = _
    rw [sectorJointBasis_weight, Matrix.mulVec_smul]
  have he := congrFun hweight w
  rw [TensorPowers.generators_diagonal, Matrix.mulVec_diagonal] at he
  change (WordTypes.content w j : ℂ) * (J *ᵥ v) w =
    sectorJointEigenvalue i a j * (J *ᵥ v) w at he
  exact (mul_right_cancel₀ hw he).symm

/-- The actual natural occupation label of a constructed basis vector. -/
def sectorWeight (i : Sector d n) (a : SectorSpace d n i) : Occupation d n :=
  (sectorJointEigenvalue_is_occupation i a).choose

theorem sectorJointEigenvalue_eq_weight (i : Sector d n) (a : SectorSpace d n i) (j : Fin d) :
    sectorJointEigenvalue i a j = ((sectorWeight i a).val j : ℂ) :=
  (sectorJointEigenvalue_is_occupation i a).choose_spec j

/-- Literal unitary change of coordinates to the constructed weight basis. -/
def sectorWeightUnitary (i : Sector d n) : Matrix (SectorSpace d n i) (SectorSpace d n i) ℂ :=
  fun a b => sectorJointBasis i b a

theorem sectorWeightUnitary_isometry (i : Sector d n) :
    (sectorWeightUnitary i)ᴴ * sectorWeightUnitary i = 1 := by
  ext a b
  have h := (sectorJointBasis i).inner_eq_ite a b
  simpa only [sectorWeightUnitary, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Matrix.one_apply, PiLp.inner_apply, RCLike.inner_apply', RCLike.star_def] using h

theorem sectorWeightUnitary_coisometry (i : Sector d n) :
    sectorWeightUnitary i * (sectorWeightUnitary i)ᴴ = 1 :=
  mul_eq_one_comm.mp (sectorWeightUnitary_isometry i)

/-- The actual diagonal generators become literal natural-weight diagonal
matrices in the constructed unitary basis. -/
theorem sectorWeightUnitary_diagonal (i : Sector d n) (j : Fin d) :
    (sectorWeightUnitary i)ᴴ * (sectorGenerators i).E j j * sectorWeightUnitary i =
      Matrix.diagonal (fun a => ((sectorWeight i a).val j : ℂ)) := by
  have h : (sectorGenerators i).E j j * sectorWeightUnitary i =
      sectorWeightUnitary i * Matrix.diagonal (fun a => ((sectorWeight i a).val j : ℂ)) := by
    ext a b
    rw [Matrix.mul_diagonal]
    have hb := congrFun (sectorJointBasis_weight i b j) a
    simpa only [Matrix.mul_apply, sectorWeightUnitary,
      Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul,
      sectorJointEigenvalue_eq_weight, mul_comm] using hb
  rw [Matrix.mul_assoc, h, ← Matrix.mul_assoc, sectorWeightUnitary_isometry, Matrix.one_mul]

end FreeEntropy.SchurWeyl
