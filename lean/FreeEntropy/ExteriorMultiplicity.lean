/-
Copyright (c) 2026 Free Entropy formalization contributors.
See LICENSE and NOTICE in the repository root for license and attribution.
-/

import FreeEntropy.ExteriorCanonicalCyclicity
import FreeEntropy.ExteriorWeightDimension
import FreeEntropy.LiePBWMultiplicity

/-! Exact shallow weight multiplicities for the concrete exterior irreducible
representations. The upper bound is PBW; the lower bound is the independently
constructed family of lower-unipotent root monomials. -/
noncomputable section
open Matrix
open scoped BigOperators
namespace FreeEntropy.ExteriorRepresentation
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
variable {d : ℕ}

private theorem complex_weight_eq_iff (a b : Fin d → ℕ) :
    (fun k => (a k : ℂ)) = (fun k => (b k : ℂ)) ↔ a = b := by
  constructor
  · intro h
    funext k
    exact_mod_cast congrFun h k
  · rintro rfl
    rfl

/-- An integer root shift agrees exactly with the complex eigenvalue shift. -/
theorem shiftedWeight_eq_of_difference (mu wt : Fin d → ℕ)
    (a : LowerRoot d →₀ ℕ)
    (hshift : ∀ k, (wt k : ℤ) - (mu k : ℤ) = rootWeightShift a k) :
    LiePBW.shiftedWeight (fun k => (mu k : ℂ)) a = (fun k => (wt k : ℂ)) := by
  funext k
  dsimp [LiePBW.shiftedWeight]
  have hk := hshift k
  have hc : (wt k : ℂ) - (mu k : ℂ) = (rootWeightShift a k : ℂ) := by
    exact_mod_cast hk
  linear_combination -hc

private theorem actualWeight_finrank_le_of_cyclic
    (mu wt : Fin d → ℕ) (hmu : Antitone mu) (a : LowerRoot d →₀ ℕ)
    (hshift : ∀ k, (wt k : ℤ) - (mu k : ℤ) = rootWeightShift a k)
    (hcyclic : ∀ v ∈ highestSubspace mu,
      v.ofLp ∈ LiePBW.cyclicSpan (ambientGenerators mu) (highestVector mu).ofLp) :
    Module.finrank ℂ (actualWeightSpace mu wt) ≤ (lowerWeightFiber a).card := by
  classical
  let W := LiePBW.cyclicSpan (ambientGenerators mu) (highestVector mu).ofLp ⊓
    LiePBW.coordinateWeightSpace (fun b k => (tensorWeight (columnHeight mu) b k : ℂ))
      (LiePBW.shiftedWeight (fun k => (mu k : ℂ)) a)
  let f : actualWeightSpace mu wt →ₗ[ℂ] W :=
    { toFun := fun v => ⟨v.val.ofLp, hcyclic v.val v.property.1, by
        intro b hb
        apply v.property.2 b
        intro he
        apply hb
        rw [shiftedWeight_eq_of_difference mu wt a hshift]
        funext k
        exact congrArg (fun p : Fin d → ℕ => (p k : ℂ)) he⟩
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }
  have hf : Function.Injective f := by
    intro v w h
    apply Subtype.ext
    exact WithLp.ofLp_injective 2 (congrArg Subtype.val h)
  apply (LinearMap.finrank_le_finrank_of_injective hf).trans
  apply LiePBW.cyclic_weightSpace_finrank_le_rootFiber (ambientGenerators mu)
    (fun b k => (tensorWeight (columnHeight mu) b k : ℂ))
    (ambientGenerators_diagonal mu) (fun k => (mu k : ℂ)) (highestVector mu).ofLp
  · intro k
    simpa only [highestBasisIndex, tensorFirst_weight mu hmu] using ambientHighest_weight mu k
  · exact ambientHighest_raise mu

/-- Natural weight coordinates are determined by their signed difference
from the highest row. -/
theorem weight_eq_of_difference (mu wt wt' : Fin d → ℕ)
    (h : ∀ k, (wt k : ℤ) - (mu k : ℤ) = (wt' k : ℤ) - (mu k : ℤ)) :
    wt = wt' := by
  funext k
  exact Int.ofNat_inj.mp (sub_left_inj.mp (h k))

/-- The PBW bound applies to the literal weight space of the actually
constructed exterior irreducible; no representation or multiplicity premise
remains. -/
theorem actualWeight_finrank_le_rootFiber
    (mu wt : Fin d → ℕ) (hmu : Antitone mu) (a : LowerRoot d →₀ ℕ)
    (hshift : ∀ k, (wt k : ℤ) - (mu k : ℤ) = rootWeightShift a k) :
    Module.finrank ℂ (actualWeightSpace mu wt) ≤ (lowerWeightFiber a).card := by
  apply actualWeight_finrank_le_of_cyclic mu wt hmu a hshift
  intro v hv
  rw [ambientHighest_cyclic]
  exact ⟨v, hv, rfl⟩

/-- At every feasible shallow weight the concrete representation has exactly
the positive-root partition multiplicity. -/
theorem shallow_actualWeight_finrank_eq_rootFiber
    (mu wt : Fin d → ℕ) (hmu : Antitone mu) (g : ℕ)
    (hgap : ∀ j : Fin d, ∀ hj : j.val + 1 < d, g + mu ⟨j.val + 1, hj⟩ ≤ mu j)
    (a : LowerRoot d →₀ ℕ) (ha : rootDepth a ≤ g)
    (hshift : ∀ k, (wt k : ℤ) - (mu k : ℤ) = rootWeightShift a k) :
    Module.finrank ℂ (actualWeightSpace mu wt) = (lowerWeightFiber a).card := by
  apply Nat.le_antisymm (actualWeight_finrank_le_rootFiber mu wt hmu a hshift)
  have hlo := lowerWeightFiber_card_le_weight_finrank mu hmu g hgap a ha
  have he : tensorWeight (columnHeight mu) (shallowMonomialBasis mu a hmu g hgap ha) = wt := by
    apply weight_eq_of_difference mu
    intro k
    exact (shallowMonomialBasis_weight_difference mu a hmu g hgap ha k).trans (hshift k).symm
  exact hlo.trans_eq (congrArg (fun w => Module.finrank ℂ (actualWeightSpace mu w)) he)

/-- The exact multiplicity theorem also permits unused zero-tail rows: a
gap is required only at roots that can contribute to the chosen weight. -/
theorem supported_actualWeight_finrank_eq_rootFiber
    (mu wt : Fin d → ℕ) (hmu : Antitone mu) (g : ℕ)
    (a : LowerRoot d →₀ ℕ) (ha : rootDepth a ≤ g)
    (hgap : ∀ b ∈ lowerWeightFiber a, ∀ r : LowerRoot d,
      b r ≠ 0 → g + mu (rootNext r) ≤ mu r.val.1)
    (hshift : ∀ k, (wt k : ℤ) - (mu k : ℤ) = rootWeightShift a k) :
    Module.finrank ℂ (actualWeightSpace mu wt) = (lowerWeightFiber a).card := by
  apply Nat.le_antisymm (actualWeight_finrank_le_rootFiber mu wt hmu a hshift)
  have hlo := supported_lowerWeightFiber_card_le_weight_finrank mu hmu g a ha hgap
  have he : tensorWeight (columnHeight mu) (supportedMonomialBasis mu a hmu g
      (hgap a ((mem_lowerWeightFiber a a).mpr rfl)) ha) = wt := by
    apply weight_eq_of_difference mu
    intro k
    exact (supportedMonomialBasis_weight_difference mu a hmu g
      (hgap a ((mem_lowerWeightFiber a a).mpr rfl)) ha k).trans (hshift k).symm
  exact hlo.trans_eq (congrArg (fun w => Module.finrank ℂ (actualWeightSpace mu w)) he)

/-- Rank-deficient highest rows require only their positive-rank adjacent
gaps. The root support in the zero-change tail is derived, not assumed. -/
theorem rank_supported_actualWeight_finrank_eq_rootFiber
    (mu wt : Fin d → ℕ) (hmu : Antitone mu) (g rank : ℕ)
    (hgap : ∀ j : Fin d, ∀ hj : j.val + 1 < d,
      j.val + 1 < rank → g + mu ⟨j.val + 1, hj⟩ ≤ mu j)
    (a : LowerRoot d →₀ ℕ) (ha : rootDepth a ≤ g)
    (hshift : ∀ k, (wt k : ℤ) - (mu k : ℤ) = rootWeightShift a k)
    (hzero : ∀ k : Fin d, rank ≤ k.val → wt k = mu k) :
    Module.finrank ℂ (actualWeightSpace mu wt) = (lowerWeightFiber a).card := by
  apply supported_actualWeight_finrank_eq_rootFiber mu wt hmu g a ha _ hshift
  intro b hb r hr
  have htail : ∀ k : Fin d, rank ≤ k.val → rootWeightShift a k = 0 := by
    intro k hk
    rw [← hshift k, hzero k hk, sub_self]
  have hrt := lowerWeightFiber_root_support a b rank htail hb r hr
  apply hgap r.val.1 (rootNext r).isLt
  have hlt : r.val.1.val < r.val.2.val := r.property
  omega

/-- Every actual nonzero weight space supplies its own positive-root
assignment. There is no assumed root-cone or spectral-support premise. -/
theorem exists_rootAssignment_of_actualWeight_ne_bot
    (mu wt : Fin d → ℕ) (hmu : Antitone mu)
    (hne : actualWeightSpace mu wt ≠ ⊥) :
    ∃ a : LowerRoot d →₀ ℕ, ∀ k,
      (wt k : ℤ) - (mu k : ℤ) = rootWeightShift a k := by
  classical
  obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  obtain ⟨b, hb⟩ : ∃ b, v b ≠ 0 := by
    by_contra hn
    push_neg at hn
    apply hv0
    exact PiLp.ext hn
  have hc : v.ofLp ∈ LiePBW.cyclicSpan (ambientGenerators mu) (highestVector mu).ofLp := by
    rw [ambientHighest_cyclic]
    exact ⟨v, hv.1, rfl⟩
  have hw (k : Fin d) : (ambientGenerators mu).E k k *ᵥ (highestVector mu).ofLp =
      (mu k : ℂ) • (highestVector mu).ofLp := by
    simpa only [highestBasisIndex, tensorFirst_weight mu hmu] using ambientHighest_weight mu k
  obtain ⟨a, ha⟩ := LiePBW.coordinate_weight_has_assignment (ambientGenerators mu)
    (fun b k => (tensorWeight (columnHeight mu) b k : ℂ))
    (ambientGenerators_diagonal mu) (fun k => (mu k : ℂ)) (highestVector mu).ofLp
    hw (ambientHighest_raise mu) v.ofLp hc b hb
  have hbw : tensorWeight (columnHeight mu) b = wt := by
    by_contra hn
    exact hb (hv.2 b hn)
  refine ⟨a, fun k => ?_⟩
  have he := congrFun ha k
  change (tensorWeight (columnHeight mu) b k : ℂ) =
    (mu k : ℂ) + (rootWeightShift a k : ℂ) at he
  rw [congrFun hbw k] at he
  have he' : (wt k : ℂ) - (mu k : ℂ) = (rootWeightShift a k : ℂ) := by
    linear_combination he
  exact_mod_cast he'

/-- Adding a dominant row leaves every shallow multiplicity unchanged;
both sides are the same derived root-partition count. -/
theorem shallow_actualWeight_finrank_add_dominant
    (mu omega wt : Fin d → ℕ) (hmu : Antitone mu) (homega : Antitone omega) (g : ℕ)
    (hgap : ∀ j : Fin d, ∀ hj : j.val + 1 < d, g + mu ⟨j.val + 1, hj⟩ ≤ mu j)
    (a : LowerRoot d →₀ ℕ) (ha : rootDepth a ≤ g)
    (hshift : ∀ k, (wt k : ℤ) - (mu k : ℤ) = rootWeightShift a k) :
    Module.finrank ℂ (actualWeightSpace (mu + omega) (wt + omega)) =
      Module.finrank ℂ (actualWeightSpace mu wt) := by
  rw [shallow_actualWeight_finrank_eq_rootFiber mu wt hmu g hgap a ha hshift]
  refine shallow_actualWeight_finrank_eq_rootFiber (mu + omega) (wt + omega)
    (fun i j hij => Nat.add_le_add (hmu hij) (homega hij)) g ?_ a ha ?_
  · intro j hj
    have hg := hgap j hj
    have ho := homega (show j ≤ (⟨j.val + 1, hj⟩ : Fin d) by change j.val ≤ j.val + 1; omega)
    change g + (mu _ + omega _) ≤ mu _ + omega _
    omega
  · intro k
    simp only [Pi.add_apply, Nat.cast_add]
    linear_combination hshift k

/-- The same shallow multiplicity equality holds with a zero tail: only
adjacent gaps below the rank are required. -/
theorem rank_supported_actualWeight_finrank_add_dominant
    (mu omega wt : Fin d → ℕ) (hmu : Antitone mu) (homega : Antitone omega) (g rank : ℕ)
    (hgap : ∀ j : Fin d, ∀ hj : j.val + 1 < d,
      j.val + 1 < rank → g + mu ⟨j.val + 1, hj⟩ ≤ mu j)
    (a : LowerRoot d →₀ ℕ) (ha : rootDepth a ≤ g)
    (hshift : ∀ k, (wt k : ℤ) - (mu k : ℤ) = rootWeightShift a k)
    (hzero : ∀ k : Fin d, rank ≤ k.val → wt k = mu k) :
    Module.finrank ℂ (actualWeightSpace (mu + omega) (wt + omega)) =
      Module.finrank ℂ (actualWeightSpace mu wt) := by
  rw [rank_supported_actualWeight_finrank_eq_rootFiber mu wt hmu g rank hgap a ha hshift hzero]
  refine rank_supported_actualWeight_finrank_eq_rootFiber (mu + omega) (wt + omega)
    (fun i j hij => Nat.add_le_add (hmu hij) (homega hij)) g rank ?_ a ha ?_ ?_
  · intro j hj hr
    have hg := hgap j hj hr
    have ho := homega (show j ≤ (⟨j.val + 1, hj⟩ : Fin d) by change j.val ≤ j.val + 1; omega)
    change g + (mu _ + omega _) ≤ mu _ + omega _
    omega
  · intro k
    simp only [Pi.add_apply, Nat.cast_add]
    linear_combination hshift k
  · intro k hk
    simp only [Pi.add_apply, hzero k hk]

end FreeEntropy.ExteriorRepresentation
