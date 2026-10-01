/-
Copyright (c) 2026 Free Entropy formalization contributors.
See LICENSE and NOTICE in the repository root for license and attribution.
-/

import FreeEntropy.UnitaryDecompositionOrthogonal

/-! Isometric matrix realizations of the actual invariant Hilbert subspaces. -/

noncomputable section
open Matrix
open scoped BigOperators ComplexInnerProductSpace

namespace FreeEntropy.UnitaryDecomposition
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false

variable {G H : Type*} [Group G] [Fintype H] [DecidableEq H]

abbrev Subspace (H : Type*) [Fintype H] := Submodule ℂ (EuclideanSpace ℂ H)

def embedding (K : Subspace H) : Matrix H (Fin (Module.finrank ℂ K)) ℂ :=
  fun i j => ((stdOrthonormalBasis ℂ K j : K) : EuclideanSpace ℂ H) i

theorem embedding_isometry (K : Subspace H) : (embedding K)ᴴ * embedding K = 1 := by
  ext i j
  have hb := (stdOrthonormalBasis ℂ K).inner_eq_ite i j
  simpa only [embedding, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply,
    Submodule.coe_inner, PiLp.inner_apply, RCLike.inner_apply', RCLike.star_def] using hb

theorem embedding_orthogonal {K L : Subspace H} (h : Orthogonal K L) :
    (embedding K)ᴴ * embedding L = 0 := by
  ext i j
  have hb := h ((stdOrthonormalBasis ℂ K i : K) : EuclideanSpace ℂ H)
    (stdOrthonormalBasis ℂ K i).property ((stdOrthonormalBasis ℂ L j : L) : EuclideanSpace ℂ H)
    (stdOrthonormalBasis ℂ L j).property
  simpa only [embedding, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.zero_apply,
    PiLp.inner_apply, RCLike.inner_apply', RCLike.star_def] using hb

theorem embedding_adjoint_mulVec (K : Subspace H) (v : EuclideanSpace ℂ H)
    (j : Fin (Module.finrank ℂ K)) :
    ((embedding K)ᴴ *ᵥ v.ofLp) j = ⟪((stdOrthonormalBasis ℂ K j : K) : EuclideanSpace ℂ H), v⟫ := by
  simp only [embedding, Matrix.mulVec, dotProduct, Matrix.conjTranspose_apply,
    PiLp.inner_apply, RCLike.inner_apply', RCLike.star_def]

/-- The column-isometry projection is the actual Hilbert-space projection. -/
theorem embedding_projection (K : Subspace H) (v : EuclideanSpace ℂ H) :
    Matrix.toEuclideanLin (embedding K * (embedding K)ᴴ) v = K.starProjection v := by
  have hp := (stdOrthonormalBasis ℂ K).orthogonalProjection_apply_eq_sum v
  rw [Matrix.toLpLin_apply, ← Matrix.mulVec_mulVec]
  apply WithLp.ofLp_injective 2
  funext i
  change (∑ j, embedding K i j * (((embedding K)ᴴ *ᵥ v.ofLp) j)) = _
  simp only [embedding_adjoint_mulVec]
  have h := congrArg (fun w : K => ((w : EuclideanSpace ℂ H) i)) hp
  simpa only [Submodule.starProjection_apply, embedding, Submodule.coe_sum, WithLp.ofLp_sum, Finset.sum_apply,
    Submodule.coe_smul, WithLp.ofLp_smul, Pi.smul_apply, smul_eq_mul, mul_comm] using h.symm

/-- Every embedded vector lies in the subspace whose basis defines the embedding. -/
theorem embedding_mulVec_mem (K : Subspace H) (v : Fin (Module.finrank ℂ K) → ℂ) :
    WithLp.toLp 2 (embedding K *ᵥ v) ∈ K := by
  have hp := embedding_projection K (WithLp.toLp 2 (embedding K *ᵥ v))
  have he : Matrix.toEuclideanLin (embedding K * (embedding K)ᴴ)
      (WithLp.toLp 2 (embedding K *ᵥ v)) = WithLp.toLp 2 (embedding K *ᵥ v) := by
    simp only [Matrix.toLpLin_apply, Matrix.mulVec_mulVec, Matrix.mul_assoc,
      embedding_isometry, Matrix.mul_one]
  rw [he] at hp
  exact hp ▸ K.starProjection_apply_mem _

def compressed (U : G →* Matrix H H ℂ) (K : Subspace H) (g : G) :
    Matrix (Fin (Module.finrank ℂ K)) (Fin (Module.finrank ℂ K)) ℂ :=
  (embedding K)ᴴ * U g * embedding K

theorem embedding_intertwines (U : G →* Matrix H H ℂ) (K : Subspace H)
    (hK : Invariant (euclideanRepresentation U) K) (g : G) :
    U g * embedding K = embedding K * compressed U K g := by
  have hpres : (embedding K * (embedding K)ᴴ) * (U g * embedding K) = U g * embedding K := by
    ext i j
    have hp := Submodule.starProjection_eq_self_iff.mpr
      (hK g ((stdOrthonormalBasis ℂ K j : K) : EuclideanSpace ℂ H)
        (stdOrthonormalBasis ℂ K j).property)
    have he := (embedding_projection K
      (Matrix.toEuclideanLin (U g) ((stdOrthonormalBasis ℂ K j : K) : EuclideanSpace ℂ H))).trans hp
    have hv := congrArg (fun v : EuclideanSpace ℂ H => v i) he
    simpa only [Matrix.toLpLin_apply, Matrix.mul_apply, Matrix.mulVec, dotProduct, embedding] using hv
  simpa only [compressed, Matrix.mul_assoc] using hpres.symm


/-- The coordinate action on the actual invariant subspace. -/
def restrictedMatrix (U : G →* Matrix H H ℂ) (K : Subspace H)
    (hK : Invariant (euclideanRepresentation U) K) :
    G →* Matrix (Fin (Module.finrank ℂ K)) (Fin (Module.finrank ℂ K)) ℂ where
  toFun := compressed U K
  map_one' := by simp [compressed, embedding_isometry]
  map_mul' g h := by
    change (embedding K)ᴴ * U (g * h) * embedding K = _
    rw [map_mul, Matrix.mul_assoc, Matrix.mul_assoc, embedding_intertwines U K hK h]
    simp only [compressed, Matrix.mul_assoc]

@[simp] theorem restrictedMatrix_apply (U : G →* Matrix H H ℂ) (K : Subspace H)
    (hK : Invariant (euclideanRepresentation U) K) (g : G) :
    restrictedMatrix U K hK g = (embedding K)ᴴ * U g * embedding K := rfl

theorem restrictedMatrix_unitary (U : G →* Matrix H H ℂ)
    (hunitary : ∀ g, (U g)ᴴ * U g = 1) (K : Subspace H)
    (hK : Invariant (euclideanRepresentation U) K) (g : G) :
    (restrictedMatrix U K hK g)ᴴ * restrictedMatrix U K hK g = 1 := by
  have hstar : (restrictedMatrix U K hK g)ᴴ = restrictedMatrix U K hK g⁻¹ := by
    simp only [restrictedMatrix_apply, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
      ← Twirling.inverse_eq_conjTranspose U hunitary g, Matrix.mul_assoc]
  rw [hstar, ← map_mul, inv_mul_cancel, map_one]

open scoped Matrix.Norms.Elementwise in
 theorem restrictedMatrix_continuous [TopologicalSpace G] (U : G →* Matrix H H ℂ)
    (hcontinuous : Continuous U) (K : Subspace H)
    (hK : Invariant (euclideanRepresentation U) K) :
    Continuous (restrictedMatrix U K hK) := by
  exact (continuous_const.matrix_mul hcontinuous).matrix_mul continuous_const

/-- Coordinates mapped isometrically into the genuine subspace, as a linear map. -/
def embeddingLinearMap (K : Subspace H) : (Fin (Module.finrank ℂ K) → ℂ) →ₗ[ℂ] K where
  toFun x := ⟨WithLp.toLp 2 (embedding K *ᵥ x), embedding_mulVec_mem K x⟩
  map_add' x y := by apply Subtype.ext; simp [Matrix.mulVec_add]
  map_smul' c x := by apply Subtype.ext; simp [Matrix.mulVec_smul]

theorem embeddingLinearMap_bijective (K : Subspace H) :
    Function.Bijective (embeddingLinearMap K) := by
  constructor
  · intro x y h
    have he := congrArg (fun v : K => ((v : EuclideanSpace ℂ H).ofLp)) h
    change embedding K *ᵥ x = embedding K *ᵥ y at he
    have ha := congrArg (fun v => (embedding K)ᴴ *ᵥ v) he
    simpa only [Matrix.mulVec_mulVec, embedding_isometry, Matrix.one_mulVec] using ha
  · intro y
    refine ⟨(embedding K)ᴴ *ᵥ (y : EuclideanSpace ℂ H).ofLp, ?_⟩
    apply Subtype.ext
    have hp := embedding_projection K (y : EuclideanSpace ℂ H)
    rw [Submodule.starProjection_eq_self_iff.mpr y.property] at hp
    simpa only [embeddingLinearMap, LinearMap.coe_mk, AddHom.coe_mk,
      Matrix.toLpLin_apply, Matrix.mulVec_mulVec] using hp

def coordinateIntertwiner (U : G →* Matrix H H ℂ) (K : Subspace H)
    (hK : Invariant (euclideanRepresentation U) K) :
    Representation.IntertwiningMap (Twirling.matrixRepresentation (restrictedMatrix U K hK))
      (restriction (euclideanRepresentation U) K hK) where
  toLinearMap := embeddingLinearMap K
  isIntertwining' g := by
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    apply WithLp.ofLp_injective 2
    change embedding K *ᵥ (restrictedMatrix U K hK g *ᵥ x) = U g *ᵥ (embedding K *ᵥ x)
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, embedding_intertwines U K hK g]
    rfl

/-- Coordinate changes preserve genuine irreducibility; no scalar-commutant
or final irreducibility assumption is substituted for this conclusion. -/
theorem restrictedMatrix_irreducible (U : G →* Matrix H H ℂ) (K : Subspace H)
    (hK : Invariant (euclideanRepresentation U) K)
    (hirr : Representation.IsIrreducible (restriction (euclideanRepresentation U) K hK)) :
    Representation.IsIrreducible (Twirling.matrixRepresentation (restrictedMatrix U K hK)) := by
  let f := coordinateIntertwiner U K hK
  let l := Representation.IntertwiningMap.equivLinearMapAsModule _ _ f
  have hb : Function.Bijective l := embeddingLinearMap_bijective K
  apply (Representation.irreducible_iff_isSimpleModule_asModule _).mpr
  apply (LinearMap.isSimpleModule_iff_of_bijective l hb).mpr
  exact (Representation.irreducible_iff_isSimpleModule_asModule _).mp hirr

theorem embedding_resolution (s : Finset (Subspace H))
    (horth : ∀ K ∈ s, ∀ L ∈ s, K ≠ L → Orthogonal K L)
    (hspan : s.sup id = ⊤) :
    (∑ K : s, embedding K.val * (embedding K.val)ᴴ) = 1 := by
  apply Matrix.toEuclideanLin.injective
  apply LinearMap.ext
  intro x
  have h := sum_projections_eq_identity s horth hspan x
  rw [map_sum, LinearMap.sum_apply]
  change (∑ K : s, Matrix.toEuclideanLin (embedding K.val * (embedding K.val)ᴴ) x) = _
  simp only [embedding_projection]
  simpa only [Matrix.toLpLin_apply, Matrix.one_mulVec, WithLp.toLp_ofLp] using h

end FreeEntropy.UnitaryDecomposition

