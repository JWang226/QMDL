/-
Copyright (c) 2026 Free Entropy formalization contributors.
See LICENSE and NOTICE in the repository root for license and attribution.
-/

import FreeEntropy.ExteriorMonomialWeights
import FreeEntropy.ExteriorCommutant
import FreeEntropy.PolynomialOrbitDimension
import FreeEntropy.TorusWeightProjection
import FreeEntropy.ExteriorSupportedMonomials
import FreeEntropy.ExteriorRootSupport

/-! Explicit root monomials give lower bounds for the dimensions of the
actual weight spaces of the constructed irreducible representations. -/
noncomputable section
open Matrix
open scoped BigOperators
namespace FreeEntropy.ExteriorRepresentation
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
variable {d : ℕ}

/-- The actual fixed-weight subspace inside the canonical irreducible space. -/
def actualWeightSpace (mu a : Fin d → ℕ) :
    Submodule ℂ (EuclideanSpace ℂ (AmbientIndex mu)) :=
  highestSubspace mu ⊓ TorusWeights.weightSpace (tensorWeight (columnHeight mu)) a

/-- Project the literal lower-unipotent orbit onto its genuine weight space. -/
def projectedRootOrbit (mu a : Fin d → ℕ) (x : LowerRoot d → ℂ) : actualWeightSpace mu a :=
  ⟨Matrix.toEuclideanLin (TorusWeights.projector (tensorWeight (columnHeight mu)) a)
    (Matrix.toEuclideanLin (tensorMatrix (columnHeight mu) (lowerRootMatrix x)) (highestVector mu)),
    ⟨TorusWeights.projector_mem (ambientRepresentation mu) (ambientRepresentation_unitary mu)
      Occupation.diagonalUnitary (tensorWeight (columnHeight mu))
      (fun z _ => tensorMatrix_diagonal (columnHeight mu) z)
      (highestSubspace mu) (highestSubspace_irreducible mu).invariant a _
      (matrix_highest_mem mu (lowerRootMatrix x)),
      TorusWeights.projector_mem_weightSpace _ _ _⟩⟩

def weightCoordinate (mu a : Fin d → ℕ) (b : AmbientIndex mu) :
    Module.Dual ℂ (actualWeightSpace mu a) where
  toFun v := v.val b
  map_add' := by intros; rfl
  map_smul' := by intros; rfl

theorem projectedRootOrbit_coordinate (mu a : Fin d → ℕ) (b : AmbientIndex mu)
    (hb : tensorWeight (columnHeight mu) b = a) (x : LowerRoot d → ℂ) :
    weightCoordinate mu a b (projectedRootOrbit mu a x) =
      tensorMatrix (columnHeight mu) (lowerRootMatrix x) b (highestBasisIndex mu) := by
  classical
  simp [weightCoordinate, projectedRootOrbit, TorusWeights.projector,
    Matrix.toLpLin_apply, Matrix.mulVec_diagonal, hb,
    highestVector, TorusWeights.highestVector, Matrix.mulVec_single]

/-- Each distinct feasible root monomial contributes an independent
direction in the actual selected weight space. All orbit and projection
invariance used here have been proved for the canonical representations. -/
theorem monomial_family_card_le_weight_finrank {I : Type*} [Fintype I]
    (mu a : Fin d → ℕ) (exponent : I → LowerRoot d →₀ ℕ)
    (hinj : Function.Injective exponent)
    (hcapacity : ∀ i k,
      Fintype.card {x : RootCopies (exponent i) // rootCopyHeight (exponent i) x = k} ≤ heightFiber mu k)
    (hweight : ∀ i, tensorWeight (columnHeight mu)
      (monomialBasis mu (exponent i) (hcapacity i)) = a) :
    Fintype.card I ≤ Module.finrank ℂ (actualWeightSpace mu a) := by
  apply PolynomialOrbit.card_le_finrank_of_monomial_orbit
    (fun i => weightCoordinate mu a (monomialBasis mu (exponent i) (hcapacity i)))
    (projectedRootOrbit mu a) exponent hinj
  intro i x
  rw [projectedRootOrbit_coordinate mu a _ (hweight i),
    monomialBasis_coefficient mu (exponent i) (hcapacity i) _
      (lowerRootMatrix_upper x) (lowerRootMatrix_diagonal x)]
  simp only [lowerRootMatrix_root, MvPolynomial.eval_monomial, one_mul]
  exact (Finsupp.prod_fintype (exponent i) (fun r n => x r ^ n) (by simp)).symm

/-- A finite set of shallow assignments at one root offset injects
linearly into an actual weight space. This is a genuine dimension bound,
not a GT-count identification assumption. -/
theorem shallow_monomials_card_le_weight_finrank
    (mu : Fin d → ℕ) (hmu : Antitone mu) (g : ℕ)
    (hgap : ∀ j : Fin d, ∀ hj : j.val + 1 < d, g + mu ⟨j.val + 1, hj⟩ ≤ mu j)
    (s : Finset (LowerRoot d →₀ ℕ)) (a₀ : LowerRoot d →₀ ℕ)
    (ha₀ : rootDepth a₀ ≤ g) (hs : ∀ a ∈ s, rootDepth a ≤ g)
    (hoffset : ∀ a ∈ s, rootWeightShift a = rootWeightShift a₀) :
    s.card ≤ Module.finrank ℂ (actualWeightSpace mu
      (tensorWeight (columnHeight mu) (shallowMonomialBasis mu a₀ hmu g hgap ha₀))) := by
  classical
  simpa using monomial_family_card_le_weight_finrank mu
    (tensorWeight (columnHeight mu) (shallowMonomialBasis mu a₀ hmu g hgap ha₀))
    (fun a : s => a.val) Subtype.val_injective
    (fun a => shallow_root_capacity mu a.val hmu g hgap (hs a.val a.property))
    (fun a => shallowMonomialBasis_weight_eq mu a.val a₀ hmu g hgap
      (hs a.val a.property) ha₀ (hoffset a.val a.property))

/-- Every assignment with this signed weight shift occurs independently,
provided the row gaps accommodate its (common) shallow depth. -/
theorem lowerWeightFiber_card_le_weight_finrank
    (mu : Fin d → ℕ) (hmu : Antitone mu) (g : ℕ)
    (hgap : ∀ j : Fin d, ∀ hj : j.val + 1 < d, g + mu ⟨j.val + 1, hj⟩ ≤ mu j)
    (a₀ : LowerRoot d →₀ ℕ) (ha₀ : rootDepth a₀ ≤ g) :
    (lowerWeightFiber a₀).card ≤ Module.finrank ℂ (actualWeightSpace mu
      (tensorWeight (columnHeight mu) (shallowMonomialBasis mu a₀ hmu g hgap ha₀))) := by
  apply shallow_monomials_card_le_weight_finrank mu hmu g hgap
    (lowerWeightFiber a₀) a₀ ha₀
  · intro a ha
    rw [rootDepth_eq_of_weightShift_eq a a₀ ((mem_lowerWeightFiber a₀ a).mp ha)]
    exact ha₀
  · intro a ha
    exact (mem_lowerWeightFiber a₀ a).mp ha

/-- The same actual lower dimension bound requires gaps only at roots
used by the weight fiber; unused zero tails impose no gap condition. -/
theorem supported_lowerWeightFiber_card_le_weight_finrank
    (mu : Fin d → ℕ) (hmu : Antitone mu) (g : ℕ)
    (a₀ : LowerRoot d →₀ ℕ) (ha₀ : rootDepth a₀ ≤ g)
    (hgap : ∀ a ∈ lowerWeightFiber a₀, ∀ r : LowerRoot d,
      a r ≠ 0 → g + mu (rootNext r) ≤ mu r.val.1) :
    (lowerWeightFiber a₀).card ≤ Module.finrank ℂ (actualWeightSpace mu
      (tensorWeight (columnHeight mu) (supportedMonomialBasis mu a₀ hmu g
        (hgap a₀ ((mem_lowerWeightFiber a₀ a₀).mpr rfl)) ha₀))) := by
  classical
  have hdepth (a : LowerRoot d →₀ ℕ) (ha : a ∈ lowerWeightFiber a₀) : rootDepth a ≤ g := by
    rw [rootDepth_eq_of_weightShift_eq a a₀ ((mem_lowerWeightFiber a₀ a).mp ha)]
    exact ha₀
  simpa only [Fintype.card_coe] using monomial_family_card_le_weight_finrank mu
    (tensorWeight (columnHeight mu) (supportedMonomialBasis mu a₀ hmu g
      (hgap a₀ ((mem_lowerWeightFiber a₀ a₀).mpr rfl)) ha₀))
    (fun a : lowerWeightFiber a₀ => a.val) Subtype.val_injective
    (fun a => supported_root_capacity mu a.val hmu g (hgap a.val a.property)
      (hdepth a.val a.property)) (fun a => by
        funext k
        have h₁ := monomialBasis_weight_difference mu a.val hmu
          (supported_root_capacity mu a.val hmu g (hgap a.val a.property)
            (hdepth a.val a.property)) k
        have h₂ := supportedMonomialBasis_weight_difference mu a₀ hmu g
          (hgap a₀ ((mem_lowerWeightFiber a₀ a₀).mpr rfl)) ha₀ k
        have he := congrFun ((mem_lowerWeightFiber a₀ a.val).mp a.property) k
        exact Int.ofNat_inj.mp (sub_left_inj.mp (h₁.trans (he.trans h₂.symm))))

/-- The padded, rank-deficient case: only adjacent gaps within the positive
rank are needed when the chosen weight has zero change in the tail. -/
theorem rank_supported_lowerWeightFiber_card_le_weight_finrank
    (mu : Fin d → ℕ) (hmu : Antitone mu) (g rank : ℕ)
    (hgap : ∀ j : Fin d, ∀ hj : j.val + 1 < d,
      j.val + 1 < rank → g + mu ⟨j.val + 1, hj⟩ ≤ mu j)
    (a₀ : LowerRoot d →₀ ℕ) (ha₀ : rootDepth a₀ ≤ g)
    (hzero : ∀ k : Fin d, rank ≤ k.val → rootWeightShift a₀ k = 0) :
    ∃ a : Fin d → ℕ,
      (∀ k, (a k : ℤ) - (mu k : ℤ) = rootWeightShift a₀ k) ∧
      (lowerWeightFiber a₀).card ≤ Module.finrank ℂ (actualWeightSpace mu a) := by
  have hg : ∀ a ∈ lowerWeightFiber a₀, ∀ r : LowerRoot d,
      a r ≠ 0 → g + mu (rootNext r) ≤ mu r.val.1 := by
    intro a ha r hr
    have hrt := lowerWeightFiber_root_support a₀ a rank hzero ha r hr
    apply hgap r.val.1 (rootNext r).isLt
    have hlt : r.val.1.val < r.val.2.val := r.property
    omega
  exact ⟨_, supportedMonomialBasis_weight_difference mu a₀ hmu g
    (hg a₀ ((mem_lowerWeightFiber a₀ a₀).mpr rfl)) ha₀,
    supported_lowerWeightFiber_card_le_weight_finrank mu hmu g a₀ ha₀ hg⟩

end FreeEntropy.ExteriorRepresentation
