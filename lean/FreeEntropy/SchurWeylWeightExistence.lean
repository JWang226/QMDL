/-
Copyright (c) 2026 Free Entropy formalization contributors.
See LICENSE and NOTICE in the repository root for license and attribution.
-/

import FreeEntropy.SchurWeylWeightMultiplicity
import FreeEntropy.UnitaryDecompositionMatrices

/-!
# A genuine weight vector in every nonzero invariant physical subspace

Orthogonal projection onto the invariant subspace commutes with the actual
unitary tensor action. Phase separation therefore makes it preserve word
contents. Projecting a nonzero coordinate onto its content gives a nonzero
vector in the subspace with one exact torus weight.
-/
noncomputable section
open scoped BigOperators ComplexOrder MatrixOrder
open Matrix
namespace FreeEntropy.SchurWeyl
open Occupation WordTypes UnitaryDecomposition
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
attribute [local instance] Classical.propDecidable
variable {d n : ℕ}

/-- Literal orthogonal projection onto one physical word-content class. -/
def contentProjection (a : Occupation d n) : Matrix (Fin n → Fin d) (Fin n → Fin d) ℂ :=
  Matrix.diagonal (fun w => if content w = a.val then 1 else 0)

@[simp] theorem contentProjection_mulVec (a : Occupation d n)
    (v : (Fin n → Fin d) → ℂ) (w : Fin n → Fin d) :
    (contentProjection a *ᵥ v) w = if content w = a.val then v w else 0 := by
  simp [contentProjection, Matrix.mulVec, dotProduct, Matrix.diagonal_apply]

/-- Every actual tensor-unitary commutant preserves each exact content space. -/
theorem TensorCommutant.commutes_contentProjection {T : Matrix (Fin n → Fin d) (Fin n → Fin d) ℂ}
    (hT : TensorCommutant T) (a : Occupation d n) :
    T * contentProjection a = contentProjection a * T := by
  ext w v
  simp only [contentProjection, Matrix.mul_diagonal, Matrix.diagonal_mul]
  by_cases h : content w = content v
  · rw [h]
    split_ifs <;> simp
  · rw [hT.entry_eq_zero w v h, zero_mul, mul_zero]

theorem invariant_projection_commutant (K : Subspace (Fin n → Fin d))
    (hK : Invariant (euclideanRepresentation (physicalRepresentation d n)) K) :
    TensorCommutant (embedding K * (embedding K)ᴴ) :=
  copy_matrixUnit_commutant (restrictedMatrix (physicalRepresentation d n) K hK)
    (embedding K) (embedding K) (embedding_isometry K)
    (embedding_intertwines (physicalRepresentation d n) K hK)
    (embedding_intertwines (physicalRepresentation d n) K hK)

/-- Taking a word-content component preserves every genuine invariant subspace. -/
theorem contentProjection_mem (K : Subspace (Fin n → Fin d))
    (hK : Invariant (euclideanRepresentation (physicalRepresentation d n)) K)
    (a : Occupation d n) (x : EuclideanSpace ℂ (Fin n → Fin d)) (hx : x ∈ K) :
    WithLp.toLp 2 (contentProjection a *ᵥ x.ofLp) ∈ K := by
  let y : EuclideanSpace ℂ (Fin n → Fin d) := WithLp.toLp 2 (contentProjection a *ᵥ x.ofLp)
  have hxfix : (embedding K * (embedding K)ᴴ) *ᵥ x.ofLp = x.ofLp := by
    have h := embedding_projection K x
    rw [Submodule.starProjection_eq_self_iff.mpr hx] at h
    exact congrArg WithLp.ofLp h
  have hcomm := (invariant_projection_commutant K hK).commutes_contentProjection a
  have hyfix : Matrix.toEuclideanLin (embedding K * (embedding K)ᴴ) y = y := by
    apply WithLp.ofLp_injective 2
    change (embedding K * (embedding K)ᴴ) *ᵥ (contentProjection a *ᵥ x.ofLp) =
      contentProjection a *ᵥ x.ofLp
    rw [Matrix.mulVec_mulVec, hcomm, ← Matrix.mulVec_mulVec, hxfix]
  have hp := embedding_projection K y
  rw [hyfix] at hp
  change y ∈ K
  rw [hp]
  exact K.starProjection_apply_mem y

/-- A vector supported on one content has the corresponding exact torus weight. -/
theorem supported_torus_eigenvector (a : Occupation d n) (v : (Fin n → Fin d) → ℂ)
    (hv : ∀ w, content w ≠ a.val → v w = 0)
    (z : Fin d → ℂ) (hz : ∀ i, ‖z i‖ = 1) :
    TensorPowers.matrix n (diagonalUnitary z hz).val *ᵥ v = character z a • v := by
  change TensorPowers.matrix n (Matrix.diagonal z) *ᵥ v = _
  rw [tensor_diagonal]
  funext w
  have he : (Matrix.diagonal (TensorPowers.vector n z) *ᵥ v) w =
      TensorPowers.vector n z w * v w := by
    simp [Matrix.mulVec, dotProduct, Matrix.diagonal_apply]
  rw [he]
  by_cases hw : content w = a.val
  · have ha : ofWord w = a := Subtype.ext hw
    rw [tensorVector_eq_character, ha]
    rfl
  · simp [hv w hw]

/-- Every nonzero invariant subspace of the actual physical tensor action
contains a nonzero vector with one actual occupation weight. -/
theorem exists_weight_vector (K : Subspace (Fin n → Fin d))
    (hK : Invariant (euclideanRepresentation (physicalRepresentation d n)) K)
    (hK0 : K ≠ ⊥) :
    ∃ a : Occupation d n, ∃ v : EuclideanSpace ℂ (Fin n → Fin d),
      v ∈ K ∧ v ≠ 0 ∧ ∀ z : Fin d → ℂ, ∀ hz : ∀ i, ‖z i‖ = 1,
        TensorPowers.matrix n (diagonalUnitary z hz).val *ᵥ v.ofLp = character z a • v.ofLp := by
  obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hK0
  have hw : ∃ w, x w ≠ 0 := by
    by_contra! h
    apply hx0
    apply WithLp.ofLp_injective 2
    exact funext h
  obtain ⟨w, hw⟩ := hw
  let a := ofWord w
  let v : EuclideanSpace ℂ (Fin n → Fin d) := WithLp.toLp 2 (contentProjection a *ᵥ x.ofLp)
  refine ⟨a, v, contentProjection_mem K hK a x hx, ?_, ?_⟩
  · intro hv
    have he := congrArg (fun y : EuclideanSpace ℂ (Fin n → Fin d) => y w) hv
    have he' : v w = x w := by simp [v, a, ofWord]
    change v w = 0 at he
    rw [he'] at he
    exact hw he
  · apply supported_torus_eigenvector a v.ofLp
    intro u hu
    simp [v, hu]

end FreeEntropy.SchurWeyl
