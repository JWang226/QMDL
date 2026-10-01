/-
Copyright (c) 2026 Free Entropy formalization contributors.
See LICENSE and NOTICE in the repository root for license and attribution.
-/

import FreeEntropy.ExteriorWeightCoordinates

/-! Coordinate multiplicities equal the dimensions of the literal exterior
weight subspaces. This transports the proved PBW and monomial formulas to
the actual orthonormal matrix models used by the quantum channels. -/
noncomputable section
open Matrix
open scoped BigOperators
namespace FreeEntropy.ExteriorRepresentation
open LiePBW UnitaryDecomposition
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
variable {d : ℕ}

private theorem cast_weight_eq_iff (a b : Fin d → ℕ) :
    (fun k => (a k : ℂ)) = (fun k => (b k : ℂ)) ↔ a = b := by
  constructor
  · intro h
    funext k
    exact_mod_cast congrFun h k
  · rintro rfl
    rfl

def canonicalCoordinateWeightSpace (mu wt : Fin d → ℕ) : Submodule ℂ (IrrepIndex mu → ℂ) :=
  coordinateWeightSpace (fun a k => (canonicalWeight mu a k : ℂ)) (fun k => (wt k : ℂ))

theorem canonicalWeightEmbedding_mem (mu wt : Fin d → ℕ)
    (x : IrrepIndex mu → ℂ) (hx : x ∈ canonicalCoordinateWeightSpace mu wt) :
    WithLp.toLp 2 (canonicalWeightEmbedding mu *ᵥ x) ∈ actualWeightSpace mu wt := by
  classical
  constructor
  · change WithLp.toLp 2 ((irrepEmbedding mu * (canonicalWeightCoordinates mu).unitary) *ᵥ x) ∈ _
    rw [← Matrix.mulVec_mulVec]
    exact embedding_mulVec_mem _ _
  · intro b hb
    change ∑ a, canonicalWeightEmbedding mu b a * x a = 0
    apply Finset.sum_eq_zero
    intro a _
    by_cases ha : canonicalWeight mu a = wt
    · have hne : tensorWeight (columnHeight mu) b ≠ canonicalWeight mu a := by simpa only [ha] using hb
      rw [canonicalWeightEmbedding_supported mu b a hne, zero_mul]
    · have hne : (fun k => (canonicalWeight mu a k : ℂ)) ≠ (fun k => (wt k : ℂ)) :=
        mt (cast_weight_eq_iff _ _).mp ha
      rw [hx a hne, mul_zero]

theorem canonicalWeightEmbedding_adjoint_mem (mu wt : Fin d → ℕ)
    (x : EuclideanSpace ℂ (AmbientIndex mu)) (hx : x ∈ actualWeightSpace mu wt) :
    (canonicalWeightEmbedding mu)ᴴ *ᵥ x.ofLp ∈ canonicalCoordinateWeightSpace mu wt := by
  classical
  intro a ha
  have hne : canonicalWeight mu a ≠ wt := mt (cast_weight_eq_iff _ _).mpr ha
  change ∑ b, star (canonicalWeightEmbedding mu b a) * x b = 0
  apply Finset.sum_eq_zero
  intro b _
  by_cases hb : tensorWeight (columnHeight mu) b = wt
  · have hba : tensorWeight (columnHeight mu) b ≠ canonicalWeight mu a := by
      rw [hb]
      exact hne.symm
    rw [canonicalWeightEmbedding_supported mu b a hba, star_zero, zero_mul]
  · rw [hx.2 b hb, mul_zero]

/-- Literal isometric coordinates identify the two actual weight spaces. -/
def canonicalWeightSpaceEquiv (mu wt : Fin d → ℕ) :
    canonicalCoordinateWeightSpace mu wt ≃ₗ[ℂ] actualWeightSpace mu wt where
  toFun x := ⟨WithLp.toLp 2 (canonicalWeightEmbedding mu *ᵥ x.val),
    canonicalWeightEmbedding_mem mu wt x.val x.property⟩
  invFun x := ⟨(canonicalWeightEmbedding mu)ᴴ *ᵥ x.val.ofLp,
    canonicalWeightEmbedding_adjoint_mem mu wt x.val x.property⟩
  left_inv x := by
    apply Subtype.ext
    change (canonicalWeightEmbedding mu)ᴴ *ᵥ (canonicalWeightEmbedding mu *ᵥ x.val) = x.val
    rw [Matrix.mulVec_mulVec, canonicalWeightEmbedding_isometry, Matrix.one_mulVec]
  right_inv x := by
    apply Subtype.ext
    have hp := embedding_projection (highestSubspace mu) x.val
    rw [Submodule.starProjection_eq_self_iff.mpr x.property.1] at hp
    change WithLp.toLp 2 (canonicalWeightEmbedding mu *ᵥ
      ((canonicalWeightEmbedding mu)ᴴ *ᵥ x.val.ofLp)) = x.val
    rw [Matrix.mulVec_mulVec, canonicalWeightEmbedding_projection]
    exact hp
  map_add' x y := by apply Subtype.ext; simp [Matrix.mulVec_add]
  map_smul' c x := by apply Subtype.ext; simp [Matrix.mulVec_smul]

/-- A coordinate fiber has precisely the proved actual weight-space dimension. -/
theorem canonicalWeight_card_eq_finrank (mu wt : Fin d → ℕ) :
    Fintype.card {a : IrrepIndex mu // canonicalWeight mu a = wt} =
      Module.finrank ℂ (actualWeightSpace mu wt) := by
  classical
  calc
    _ = Fintype.card {a : IrrepIndex mu //
        (fun k => (canonicalWeight mu a k : ℂ)) = (fun k => (wt k : ℂ))} :=
      Fintype.card_congr (Equiv.subtypeEquivRight (fun a => (cast_weight_eq_iff _ _).symm))
    _ = Module.finrank ℂ (canonicalCoordinateWeightSpace mu wt) :=
      (coordinateWeightSpace_finrank _ _).symm
    _ = _ := (canonicalWeightSpaceEquiv mu wt).finrank_eq

/-- The actual orthonormal model obeys the unconditional Kostant upper bound. -/
theorem canonicalWeight_card_le_rootFiber
    (mu wt : Fin d → ℕ) (hmu : Antitone mu) (a : LowerRoot d →₀ ℕ)
    (hshift : ∀ k, (wt k : ℤ) - (mu k : ℤ) = rootWeightShift a k) :
    Fintype.card {b : IrrepIndex mu // canonicalWeight mu b = wt} ≤ (lowerWeightFiber a).card := by
  rw [canonicalWeight_card_eq_finrank]
  exact actualWeight_finrank_le_rootFiber mu wt hmu a hshift

/-- Exact shallow multiplicity, now for the matrix model's literal coordinate count. -/
theorem canonicalWeight_card_eq_rootFiber
    (mu wt : Fin d → ℕ) (hmu : Antitone mu) (g rank : ℕ)
    (hgap : ∀ j : Fin d, ∀ hj : j.val + 1 < d,
      j.val + 1 < rank → g + mu ⟨j.val + 1, hj⟩ ≤ mu j)
    (a : LowerRoot d →₀ ℕ) (ha : rootDepth a ≤ g)
    (hshift : ∀ k, (wt k : ℤ) - (mu k : ℤ) = rootWeightShift a k)
    (hzero : ∀ k : Fin d, rank ≤ k.val → wt k = mu k) :
    Fintype.card {b : IrrepIndex mu // canonicalWeight mu b = wt} = (lowerWeightFiber a).card := by
  rw [canonicalWeight_card_eq_finrank]
  exact rank_supported_actualWeight_finrank_eq_rootFiber mu wt hmu g rank hgap a ha hshift hzero

end FreeEntropy.ExteriorRepresentation
