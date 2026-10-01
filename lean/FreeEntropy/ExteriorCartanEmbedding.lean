/-
Copyright (c) 2026 Free Entropy formalization contributors.
See LICENSE and NOTICE in the repository root for license and attribution.
-/

import FreeEntropy.ExteriorCartan
import FreeEntropy.ExteriorColumnEquiv
import FreeEntropy.ExteriorMatrixIrreducible
import FreeEntropy.ExteriorTensorSum

/-! The canonical Cartan embedding is constructed from the actual exterior
representations and the height-preserving permutation of their factors. -/
noncomputable section
open Matrix
open scoped BigOperators Kronecker
namespace FreeEntropy.ExteriorRepresentation
open UnitaryDecomposition
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
set_option linter.unusedSectionVars false

section CyclicSupport
variable {G A B C : Type*} [Group G] [Fintype A] [DecidableEq A]
  [Fintype B] [DecidableEq B] [Fintype C] [DecidableEq C]

theorem unitary_intertwiner_adjoint
    (U : G →* Matrix A A ℂ) (V : G →* Matrix B B ℂ)
    (hU : ∀ g, (U g)ᴴ * U g = 1) (hV : ∀ g, (V g)ᴴ * V g = 1)
    (W : Matrix A B ℂ) (hW : ∀ g, U g * W = W * V g) (g : G) :
    Wᴴ * U g = V g * Wᴴ := by
  have h := congrArg Matrix.conjTranspose (hW g⁻¹)
  rw [Twirling.inverse_eq_conjTranspose U hU,
    Twirling.inverse_eq_conjTranspose V hV] at h
  simpa only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose] using h

theorem intertwiner_range_projection_commutes
    (U : G →* Matrix A A ℂ) (V : G →* Matrix B B ℂ)
    (hU : ∀ g, (U g)ᴴ * U g = 1) (hV : ∀ g, (V g)ᴴ * V g = 1)
    (W : Matrix A B ℂ) (hW : ∀ g, U g * W = W * V g) (g : G) :
    (W * Wᴴ) * U g = U g * (W * Wᴴ) := by
  rw [Matrix.mul_assoc, unitary_intertwiner_adjoint U V hU hV W hW g,
    ← Matrix.mul_assoc, ← hW g, Matrix.mul_assoc]

/-- An actual intertwiner maps the entire cyclic span into a commuting
projection's range once it maps the generating vector into that range. -/
theorem projection_fixes_cyclic_image
    (U : G →* Matrix A A ℂ) (V : G →* Matrix B B ℂ)
    (T : Matrix B A ℂ) (hT : ∀ g, V g * T = T * U g)
    (P : Matrix B B ℂ) (hP : ∀ g, P * V g = V g * P)
    (v : EuclideanSpace ℂ A) (hv : P *ᵥ (T *ᵥ v.ofLp) = T *ᵥ v.ofLp)
    (x : EuclideanSpace ℂ A)
    (hx : x ∈ cyclicSubspace (euclideanRepresentation U) v) :
    P *ᵥ (T *ᵥ x.ofLp) = T *ᵥ x.ofLp := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨g, rfl⟩ := hx
    change P *ᵥ (T *ᵥ (U g *ᵥ v.ofLp)) = T *ᵥ (U g *ᵥ v.ofLp)
    rw [Matrix.mulVec_mulVec v.ofLp T (U g), ← hT g, ← Matrix.mulVec_mulVec]
    rw [Matrix.mulVec_mulVec (T *ᵥ v.ofLp) P (V g), hP g, ← Matrix.mulVec_mulVec, hv]
  | zero => simp
  | add x y hx hy hx' hy' =>
    simpa only [WithLp.ofLp_add, Matrix.mulVec_add, hx', hy']
  | smul c x hx hx' =>
    simpa only [WithLp.ofLp_smul, Matrix.mulVec_smul, hx']

end CyclicSupport

variable {d : ℕ} (mu nu : Fin d → ℕ)

def pairIrrepRepresentation := pairRepresentation (irrepMatrix mu) (irrepMatrix nu)

def pairIrrepEmbedding : Matrix (AmbientIndex mu × AmbientIndex nu)
    (IrrepIndex mu × IrrepIndex nu) ℂ := irrepEmbedding mu ⊗ₖ irrepEmbedding nu

theorem pairIrrepEmbedding_isometry :
    (pairIrrepEmbedding mu nu)ᴴ * pairIrrepEmbedding mu nu = 1 := by
  rw [pairIrrepEmbedding, Matrix.conjTranspose_kronecker, ← Matrix.mul_kronecker_mul,
    irrepEmbedding_isometry, irrepEmbedding_isometry]
  simp

theorem pairIrrepEmbedding_intertwines (U : Matrix.unitaryGroup (Fin d) ℂ) :
    pairAmbientRepresentation mu nu U * pairIrrepEmbedding mu nu =
      pairIrrepEmbedding mu nu * pairIrrepRepresentation mu nu U := by
  change (_ ⊗ₖ _) * (_ ⊗ₖ _) = (_ ⊗ₖ _) * (_ ⊗ₖ _)
  rw [← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul,
    irrepEmbedding_intertwines, irrepEmbedding_intertwines]

theorem irrepProjection_highest :
    (irrepEmbedding mu * (irrepEmbedding mu)ᴴ) *ᵥ
      Pi.single (highestBasisIndex mu) 1 = Pi.single (highestBasisIndex mu) 1 := by
  have h := embedding_projection (highestSubspace mu) (highestVector mu)
  have hm : highestVector mu ∈ highestSubspace mu :=
    mem_cyclicSubspace (euclideanRepresentation (ambientRepresentation mu)) (highestVector mu)
  rw [Submodule.starProjection_eq_self_iff.mpr hm] at h
  exact congrArg (WithLp.ofLp) h

theorem pairIrrepProjection_highest :
    (pairIrrepEmbedding mu nu * (pairIrrepEmbedding mu nu)ᴴ) *ᵥ
      Pi.single (highestPair mu nu) 1 = Pi.single (highestPair mu nu) 1 := by
  rw [pairIrrepEmbedding, Matrix.conjTranspose_kronecker, ← Matrix.mul_kronecker_mul]
  ext x
  have hm := congrFun (irrepProjection_highest mu) x.1
  have hn := congrFun (irrepProjection_highest nu) x.2
  simp only [Matrix.mulVec_single_one] at hm hn ⊢
  change (irrepEmbedding mu * (irrepEmbedding mu)ᴴ) x.1 (highestBasisIndex mu) *
    (irrepEmbedding nu * (irrepEmbedding nu)ᴴ) x.2 (highestBasisIndex nu) = _
  change (irrepEmbedding mu * (irrepEmbedding mu)ᴴ) x.1 (highestBasisIndex mu) = _ at hm
  change (irrepEmbedding nu * (irrepEmbedding nu)ᴴ) x.2 (highestBasisIndex nu) = _ at hn
  rw [hm, hn]
  by_cases hx : x.1 = highestBasisIndex mu <;>
    by_cases hy : x.2 = highestBasisIndex nu <;>
    simp [highestPair, Pi.single_apply, Prod.ext_iff, hx, hy]

/-- The canonical ambient equivalence is the literal permutation of exterior
columns followed by splitting the disjoint factor index. -/
def cartanAmbientEquivalence (hmu : Antitone mu) (hnu : Antitone nu) :
    Matrix (AmbientIndex mu × AmbientIndex nu) (AmbientIndex (mu + nu)) ℂ :=
  tensorSumPermutation (columnHeight mu) (columnHeight nu) *
    tensorPermutation (columnEquiv mu nu hmu hnu) (columnEquiv_height mu nu hmu hnu)

theorem cartanAmbientEquivalence_isometry (hmu : Antitone mu) (hnu : Antitone nu) :
    (cartanAmbientEquivalence mu nu hmu hnu)ᴴ * cartanAmbientEquivalence mu nu hmu hnu = 1 := by
  rw [cartanAmbientEquivalence, Matrix.conjTranspose_mul]
  simp only [Matrix.mul_assoc, ← Matrix.mul_assoc (tensorSumPermutation _ _)ᴴ,
    tensorSumPermutation_isometry, Matrix.one_mul, tensorPermutation_isometry]

theorem cartanAmbientEquivalence_intertwines (hmu : Antitone mu) (hnu : Antitone nu)
    (U : Matrix.unitaryGroup (Fin d) ℂ) :
    pairAmbientRepresentation mu nu U * cartanAmbientEquivalence mu nu hmu hnu =
      cartanAmbientEquivalence mu nu hmu hnu * ambientRepresentation (mu + nu) U := by
  dsimp only [cartanAmbientEquivalence, pairAmbientRepresentation, pairRepresentation,
    ambientRepresentation, tensorRepresentation]
  simp only [MonoidHom.coe_mk, OneHom.coe_mk]
  rw [← Matrix.mul_assoc, tensorSumPermutation_intertwines, Matrix.mul_assoc,
    tensorPermutation_intertwines, ← Matrix.mul_assoc]

theorem cartanAmbientEquivalence_highest (hmu : Antitone mu) (hnu : Antitone nu) :
    cartanAmbientEquivalence mu nu hmu hnu *ᵥ Pi.single (highestBasisIndex (mu + nu)) 1 =
      Pi.single (highestPair mu nu) 1 := by
  rw [cartanAmbientEquivalence, ← Matrix.mulVec_mulVec]
  change tensorSumPermutation _ _ *ᵥ
    (tensorPermutation _ _ *ᵥ Pi.single (tensorFirst _ (columnHeight_le (mu + nu))) 1) = _
  rw [tensorPermutation_highest _ _ (columnHeight_le (mu + nu))
    (Sum.rec (columnHeight_le mu) (columnHeight_le nu)), tensorSumPermutation_highest]
  rfl

/-- The whole canonical highest-weight component lands in the tensor product
of the two source irreducible spaces. This is derived from its cyclic orbit. -/
theorem cartanAmbientEquivalence_supported (hmu : Antitone mu) (hnu : Antitone nu) :
    (pairIrrepEmbedding mu nu * (pairIrrepEmbedding mu nu)ᴴ) *
        (cartanAmbientEquivalence mu nu hmu hnu * irrepEmbedding (mu + nu)) =
      cartanAmbientEquivalence mu nu hmu hnu * irrepEmbedding (mu + nu) := by
  ext i j
  have h := projection_fixes_cyclic_image
    (ambientRepresentation (mu + nu)) (pairAmbientRepresentation mu nu)
    (cartanAmbientEquivalence mu nu hmu hnu)
    (cartanAmbientEquivalence_intertwines mu nu hmu hnu)
    (pairIrrepEmbedding mu nu * (pairIrrepEmbedding mu nu)ᴴ)
    (intertwiner_range_projection_commutes (pairAmbientRepresentation mu nu)
      (pairIrrepRepresentation mu nu)
      (pairRepresentation_unitary _ _ (ambientRepresentation_unitary mu) (ambientRepresentation_unitary nu))
      (pairRepresentation_unitary _ _ (irrepMatrix_unitary mu) (irrepMatrix_unitary nu))
      (pairIrrepEmbedding mu nu) (pairIrrepEmbedding_intertwines mu nu))
    (highestVector (mu + nu))
    (by change _ *ᵥ (_ *ᵥ Pi.single (highestBasisIndex _) 1) = _ *ᵥ Pi.single (highestBasisIndex _) 1
        rw [cartanAmbientEquivalence_highest, pairIrrepProjection_highest])
    ((stdOrthonormalBasis ℂ (highestSubspace (mu + nu)) j : highestSubspace (mu + nu)) :
      EuclideanSpace ℂ (AmbientIndex (mu + nu)))
    (stdOrthonormalBasis ℂ (highestSubspace (mu + nu)) j).property
  have hi := congrFun h i
  simpa only [Matrix.mul_apply, Matrix.mulVec, dotProduct, irrepEmbedding, embedding] using hi

/-- The canonical Cartan isometry, with no supplied embedding or existence
assumption, into the tensor product of the actual irreducible representations. -/
def cartanEmbedding (hmu : Antitone mu) (hnu : Antitone nu) :
    Matrix (IrrepIndex mu × IrrepIndex nu) (IrrepIndex (mu + nu)) ℂ :=
  (pairIrrepEmbedding mu nu)ᴴ * cartanAmbientEquivalence mu nu hmu hnu * irrepEmbedding (mu + nu)

theorem cartanEmbedding_isometry (hmu : Antitone mu) (hnu : Antitone nu) :
    (cartanEmbedding mu nu hmu hnu)ᴴ * cartanEmbedding mu nu hmu hnu = 1 := by
  rw [cartanEmbedding, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_conjTranspose]
  calc
    _ = (irrepEmbedding (mu + nu))ᴴ * (cartanAmbientEquivalence mu nu hmu hnu)ᴴ *
        ((pairIrrepEmbedding mu nu * (pairIrrepEmbedding mu nu)ᴴ) *
        (cartanAmbientEquivalence mu nu hmu hnu * irrepEmbedding (mu + nu))) := by
      simp only [Matrix.mul_assoc]
    _ = (irrepEmbedding (mu + nu))ᴴ * (cartanAmbientEquivalence mu nu hmu hnu)ᴴ *
        (cartanAmbientEquivalence mu nu hmu hnu * irrepEmbedding (mu + nu)) := by
      rw [cartanAmbientEquivalence_supported]
    _ = (irrepEmbedding (mu + nu))ᴴ *
        ((cartanAmbientEquivalence mu nu hmu hnu)ᴴ * cartanAmbientEquivalence mu nu hmu hnu) *
        irrepEmbedding (mu + nu) := by simp only [Matrix.mul_assoc]
    _ = 1 := by rw [cartanAmbientEquivalence_isometry, Matrix.mul_one, irrepEmbedding_isometry]

theorem cartanEmbedding_intertwines (hmu : Antitone mu) (hnu : Antitone nu)
    (U : Matrix.unitaryGroup (Fin d) ℂ) :
    (irrepMatrix mu U ⊗ₖ irrepMatrix nu U) * cartanEmbedding mu nu hmu hnu =
      cartanEmbedding mu nu hmu hnu * irrepMatrix (mu + nu) U := by
  have ha := unitary_intertwiner_adjoint (pairAmbientRepresentation mu nu)
    (pairIrrepRepresentation mu nu)
    (pairRepresentation_unitary _ _ (ambientRepresentation_unitary mu) (ambientRepresentation_unitary nu))
    (pairRepresentation_unitary _ _ (irrepMatrix_unitary mu) (irrepMatrix_unitary nu))
    (pairIrrepEmbedding mu nu) (pairIrrepEmbedding_intertwines mu nu) U
  change pairIrrepRepresentation mu nu U *
    ((pairIrrepEmbedding mu nu)ᴴ * cartanAmbientEquivalence mu nu hmu hnu * irrepEmbedding (mu + nu)) = _
  calc
    _ = (pairIrrepRepresentation mu nu U * (pairIrrepEmbedding mu nu)ᴴ) *
      cartanAmbientEquivalence mu nu hmu hnu * irrepEmbedding (mu + nu) := by simp only [Matrix.mul_assoc]
    _ = ((pairIrrepEmbedding mu nu)ᴴ * pairAmbientRepresentation mu nu U) *
      cartanAmbientEquivalence mu nu hmu hnu * irrepEmbedding (mu + nu) := by rw [ha]
    _ = (pairIrrepEmbedding mu nu)ᴴ *
      (pairAmbientRepresentation mu nu U * cartanAmbientEquivalence mu nu hmu hnu) *
      irrepEmbedding (mu + nu) := by simp only [Matrix.mul_assoc]
    _ = (pairIrrepEmbedding mu nu)ᴴ *
      (cartanAmbientEquivalence mu nu hmu hnu * ambientRepresentation (mu + nu) U) *
      irrepEmbedding (mu + nu) := by rw [cartanAmbientEquivalence_intertwines]
    _ = (pairIrrepEmbedding mu nu)ᴴ * cartanAmbientEquivalence mu nu hmu hnu *
      (ambientRepresentation (mu + nu) U * irrepEmbedding (mu + nu)) := by simp only [Matrix.mul_assoc]
    _ = (pairIrrepEmbedding mu nu)ᴴ * cartanAmbientEquivalence mu nu hmu hnu *
      (irrepEmbedding (mu + nu) * irrepMatrix (mu + nu) U) := by rw [irrepEmbedding_intertwines]
    _ = _ := by simp only [cartanEmbedding, Matrix.mul_assoc]

end FreeEntropy.ExteriorRepresentation
