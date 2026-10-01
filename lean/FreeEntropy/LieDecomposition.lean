/-
Copyright (c) 2026 Free Entropy formalization contributors.
See LICENSE and NOTICE in the repository root for license and attribution.
-/

import FreeEntropy.TensorWeightCoordinates
import FreeEntropy.UnitaryDecompositionMatrices

/-! Actual complete orthogonal decomposition for every finite matrix Lie
action with the proved adjoint relation. No semisimplicity premise is used. -/
noncomputable section
open Matrix
open scoped ComplexInnerProductSpace
namespace FreeEntropy.LieDecomposition
open LieMatrixCasimir
open UnitaryDecomposition (Orthogonal orthogonal_symm orthogonal_of_le_complement)
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
variable {d : ℕ} {H : Type*} [Fintype H] [DecidableEq H]
abbrev Space (H : Type*) [Fintype H] := Submodule ℂ (EuclideanSpace ℂ H)

def Invariant (R : Generators d H) (K : Space H) : Prop :=
  ∀ i j x, x ∈ K → Matrix.toEuclideanLin (R.E i j) x ∈ K

theorem invariant_top (R : Generators d H) : Invariant R ⊤ := fun _ _ _ _ => trivial

theorem invariant_inf {R : Generators d H} {K L : Space H}
    (hK : Invariant R K) (hL : Invariant R L) : Invariant R (K ⊓ L) :=
  fun i j x hx => ⟨hK i j x hx.1, hL i j x hx.2⟩

theorem invariant_orthogonal (R : Generators d H) {K : Space H}
    (hK : Invariant R K) : Invariant R Kᗮ := by
  intro i j x hx y hy
  rw [← LinearMap.adjoint_inner_left,
    ← Matrix.toEuclideanLin_conjTranspose_eq_adjoint, R.adjoint]
  exact hx _ (hK j i y hy)

structure IrreducibleSubspace (R : Generators d H) (K : Space H) : Prop where
  invariant : Invariant R K
  ne_bot : K ≠ ⊥
  minimal : ∀ L : Space H, Invariant R L → L ≤ K → L = ⊥ ∨ L = K

theorem exists_irreducible_le (R : Generators d H) (K : Space H)
    (hK : Invariant R K) (hK0 : K ≠ ⊥) :
    ∃ L : Space H, L ≤ K ∧ IrreducibleSubspace R L := by
  classical
  let P (n : ℕ) := ∃ L : Space H,
    Invariant R L ∧ L ≠ ⊥ ∧ L ≤ K ∧ Module.finrank ℂ L = n
  have hex : ∃ n, P n := ⟨Module.finrank ℂ K, K, hK, hK0, le_rfl, rfl⟩
  obtain ⟨L, hL, hL0, hLK, hdim⟩ := Nat.find_spec hex
  refine ⟨L, hLK, hL, hL0, ?_⟩
  intro J hJ hJL
  by_cases hJ0 : J = ⊥
  · exact Or.inl hJ0
  · right
    have hmin : Nat.find hex ≤ Module.finrank ℂ J :=
      Nat.find_min' hex ⟨J, hJ, hJ0, hJL.trans hLK, rfl⟩
    apply Submodule.eq_of_le_of_finrank_eq hJL
    exact le_antisymm (Submodule.finrank_mono hJL) (by simpa [hdim] using hmin)

/-- Decompose an arbitrary invariant subspace, not merely the ambient top.
The induction strictly reduces the actual finite dimension of the remaining
orthogonal complement at each step. -/
theorem exists_orthogonal_irreducible_family (R : Generators d H) (K : Space H) (hK : Invariant R K) :
    ∃ s : Finset (Space H),
      (∀ L ∈ s, IrreducibleSubspace R L) ∧
      (∀ L ∈ s, ∀ J ∈ s, L ≠ J → Orthogonal L J) ∧ s.sup id = K := by
  classical
  generalize hdim : Module.finrank ℂ K = N
  induction N using Nat.strong_induction_on generalizing K with
  | h N ih =>
    by_cases hzero : K = ⊥
    · subst K
      exact ⟨∅, by simp, by simp, by simp⟩
    obtain ⟨L, hLK, hL⟩ := exists_irreducible_le R K hK hzero
    let J : Space H := Lᗮ ⊓ K
    have hJ : Invariant R J := invariant_inf (invariant_orthogonal R hL.invariant) hK
    have hdimJ : Module.finrank ℂ J < N := by
      have he := Submodule.finrank_add_inf_finrank_orthogonal hLK
      have hp : 1 ≤ Module.finrank ℂ L := Submodule.one_le_finrank_iff.mpr hL.ne_bot
      change Module.finrank ℂ L + Module.finrank ℂ J = Module.finrank ℂ K at he
      omega
    obtain ⟨s, hs, hortho, hsup⟩ := ih (Module.finrank ℂ J) hdimJ J hJ rfl
    have hsJ (A : Space H) (hA : A ∈ s) : A ≤ J := by
      rw [← hsup]
      exact Finset.le_sup (f := id) hA
    have hLA (A : Space H) (hA : A ∈ s) : Orthogonal L A :=
      orthogonal_of_le_complement ((hsJ A hA).trans inf_le_left)
    refine ⟨insert L s, ?_, ?_, ?_⟩
    · intro A hA
      rcases Finset.mem_insert.mp hA with rfl | hA
      · exact hL
      · exact hs A hA
    · intro A hA B hB hne
      by_cases hAL : A = L
      · subst A
        exact hLA B ((Finset.mem_insert.mp hB).resolve_left hne.symm)
      have hAs : A ∈ s := (Finset.mem_insert.mp hA).resolve_left hAL
      by_cases hBL : B = L
      · subst B
        exact orthogonal_symm (hLA A hAs)
      exact hortho A hAs B ((Finset.mem_insert.mp hB).resolve_left hBL) hne
    · rw [Finset.sup_insert, hsup]
      exact Submodule.sup_orthogonal_inf_of_hasOrthogonalProjection hLK

/-- Every unitary representation admits a complete orthogonal irreducible
decomposition; no decomposition or representation-existence premise is used. -/
theorem exists_complete_orthogonal_family (R : Generators d H) :
    ∃ s : Finset (Space H),
      (∀ L ∈ s, IrreducibleSubspace R L) ∧
      (∀ L ∈ s, ∀ J ∈ s, L ≠ J → Orthogonal L J) ∧ s.sup id = ⊤ :=
  exists_orthogonal_irreducible_family R ⊤ (invariant_top R)


open UnitaryDecomposition (embedding embedding_isometry embedding_projection
  embedding_mulVec_mem embeddingLinearMap embeddingLinearMap_bijective)

/-- The standard isometry of an invariant subspace intertwines every
actual Lie generator with its literal compression. -/
theorem embedding_intertwines (R : Generators d H) (K : Space H)
    (hK : Invariant R K) (a b : Fin d) :
    R.E a b * embedding K = embedding K * ((embedding K)ᴴ * R.E a b * embedding K) := by
  have hpres : (embedding K * (embedding K)ᴴ) * (R.E a b * embedding K) =
      R.E a b * embedding K := by
    ext i j
    have hp := Submodule.starProjection_eq_self_iff.mpr
      (hK a b ((stdOrthonormalBasis ℂ K j : K) : EuclideanSpace ℂ H)
        (stdOrthonormalBasis ℂ K j).property)
    have he := (embedding_projection K
      (Matrix.toEuclideanLin (R.E a b) ((stdOrthonormalBasis ℂ K j : K) : EuclideanSpace ℂ H))).trans hp
    have hv := congrArg (fun v : EuclideanSpace ℂ H => v i) he
    simpa only [Matrix.toLpLin_apply, Matrix.mul_apply, Matrix.mulVec, dotProduct, embedding] using hv
  simpa only [Matrix.mul_assoc] using hpres.symm

/-- The constructed restricted matrices retain all genuine gl(d) relations. -/
def restricted (R : Generators d H) (K : Space H) (hK : Invariant R K) :
    Generators d (Fin (Module.finrank ℂ K)) where
  E i j := (embedding K)ᴴ * R.E i j * embedding K
  adjoint i j := by
    simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
      R.adjoint, Matrix.mul_assoc]
  commutator i j k l := by
    have hp (X : Matrix H H ℂ) (a b : Fin d) :
        ((embedding K)ᴴ * X * embedding K) *
          ((embedding K)ᴴ * R.E a b * embedding K) =
          (embedding K)ᴴ * (X * R.E a b) * embedding K := by
      calc
        _ = (embedding K)ᴴ * X *
            (embedding K * ((embedding K)ᴴ * R.E a b * embedding K)) := by
          simp only [Matrix.mul_assoc]
        _ = _ := by rw [← embedding_intertwines R K hK]; simp only [Matrix.mul_assoc]
    rw [hp, hp, ← Matrix.sub_mul, ← Matrix.mul_sub, R.commutator]
    split_ifs <;> simp [Matrix.mul_sub, Matrix.sub_mul]

/-- Nonzero vectors in the actual irreducible restricted Lie module are
cyclic, by minimality of the ambient invariant subspace. -/
theorem restricted_cyclicSpan_eq_top (R : Generators d H) (K : Space H)
    (hK : IrreducibleSubspace R K) (v : Fin (Module.finrank ℂ K) → ℂ) (hv : v ≠ 0) :
    LiePBW.cyclicSpan (restricted R K hK.invariant) v = ⊤ := by
  let F := restricted R K hK.invariant
  let S := LiePBW.cyclicSpan F v
  let f : (Fin (Module.finrank ℂ K) → ℂ) →ₗ[ℂ] EuclideanSpace ℂ H :=
    K.subtype.comp (embeddingLinearMap K)
  have hf : Function.Injective f := K.subtype_injective.comp (embeddingLinearMap_bijective K).1
  let L : Space H := S.map f
  have hLK : L ≤ K := by
    rintro x ⟨y, hy, rfl⟩
    exact (embeddingLinearMap K y).property
  have hL : Invariant R L := by
    intro i j x hx
    obtain ⟨y, hy, rfl⟩ := hx
    refine ⟨F.E i j *ᵥ y, LiePBW.generator_preserves_cyclicSpan F v i j hy, ?_⟩
    apply WithLp.ofLp_injective 2
    change embedding K *ᵥ (F.E i j *ᵥ y) = R.E i j *ᵥ (embedding K *ᵥ y)
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, embedding_intertwines R K hK.invariant]
    rfl
  have heq : L = K := by
    rcases hK.minimal L hL hLK with hz | he
    · have hm : f v ∈ L := ⟨v, LiePBW.self_mem_cyclicSpan F v, rfl⟩
      rw [hz] at hm
      exact (hv (hf (by simpa using hm))).elim
    · exact he
  apply top_unique
  intro x _
  have hm : f x ∈ L := heq.symm ▸ (embeddingLinearMap K x).property
  obtain ⟨y, hy, hyx⟩ := hm
  exact hf hyx ▸ hy

end FreeEntropy.LieDecomposition
