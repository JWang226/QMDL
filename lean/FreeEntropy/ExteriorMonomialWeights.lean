/-
Copyright (c) 2026 Free Entropy formalization contributors.
See LICENSE and NOTICE in the repository root for license and attribution.
-/

import FreeEntropy.ExteriorMonomialColumns

/-! The explicitly constructed monomial coordinates have exactly the expected
highest-weight minus root-offset weight, so monomials with one offset give
distinct directions in one actual weight space. -/
noncomputable section
open Matrix
open scoped BigOperators
namespace FreeEntropy.ExteriorRepresentation
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
set_option linter.unusedSectionVars false
variable {d : ℕ}

@[simp] theorem weight_indexCast {k l : ℕ} (h : k = l) (s : Index d k) (i : Fin d) :
    weight (indexCast h s) i = weight s i := by subst l; rfl

theorem mem_replacement_iff (i j : Fin d) (hji : j ≤ i) (k : Fin d) :
    k ∈ (replacementSubset i j hji).val ↔ k.val < j.val ∨ k = i := by
  change k ∈ replacementSubset i j hji ↔ _
  rw [replacementSubset, Set.powersetCard.mem_ofFinEmbEquiv_iff_mem_range]
  constructor
  · rintro ⟨t, rfl⟩
    by_cases ht : t.val < j.val
    · left
      simpa [replacementEmbedding, ht] using ht
    · right
      simp [replacementEmbedding, ht]
  · rintro (hk | rfl)
    · refine ⟨⟨k.val, by omega⟩, ?_⟩
      simpa [replacementEmbedding, hk]
    · exact ⟨Fin.last j.val, replacementEmbedding_last k j hji⟩

theorem replacement_weight_difference (i j : Fin d) (hji : j < i) (k : Fin d) :
    (weight (replacementSubset i j hji.le) k : ℤ) -
      (weight (first (Nat.succ_le_of_lt j.isLt)) k : ℤ) =
        (if k = i then 1 else 0) - (if k = j then 1 else 0) := by
  have hjiv : j.val < i.val := hji
  simp only [weight, mem_replacement_iff, mem_first_iff]
  by_cases hki : k = i
  · subst k
    have hnot : ¬i.val < j.val + 1 := by omega
    simp [ne_of_gt hji, hnot]
  · by_cases hkj : k = j
    · subst k
      simp [hki]
    · by_cases hkjv : k.val < j.val
      · have hlt : k.val < j.val + 1 := by omega
        simp [hki, hkj, hkjv, hlt]
      · have hne : k.val ≠ j.val := fun h => hkj (Fin.ext h)
        have hnot : ¬k.val < j.val + 1 := by omega
        simp [hki, hkj, hkjv, hnot]

/-- The actual signed coordinate change caused by a root assignment. -/
def rootWeightShift (a : LowerRoot d →₀ ℕ) (k : Fin d) : ℤ :=
  ∑ r : LowerRoot d, (a r : ℤ) * ((if k = r.val.2 then 1 else 0) - (if k = r.val.1 then 1 else 0))

variable (mu : Fin d → ℕ) (a : LowerRoot d →₀ ℕ)

theorem monomialBasis_weight_difference (hmu : Antitone mu)
    (hcapacity : ∀ k, Fintype.card {x : RootCopies a // rootCopyHeight a x = k} ≤ heightFiber mu k)
    (k : Fin d) :
    (tensorWeight (columnHeight mu) (monomialBasis mu a hcapacity) k : ℤ) - (mu k : ℤ) =
      rootWeightShift a k := by
  have hi (x : RootCopies a) :
      (weight (monomialBasis mu a hcapacity (rootColumnEmbedding mu a hcapacity x)) k : ℤ) -
        (weight (first (columnHeight_le mu (rootColumnEmbedding mu a hcapacity x))) k : ℤ) =
      (if k = x.1.val.2 then 1 else 0) - (if k = x.1.val.1 then 1 else 0) := by
    rw [monomialBasis_at]
    rw [← indexCast_first (rootColumnEmbedding_height mu a hcapacity x).symm
      (Nat.succ_le_of_lt x.1.val.1.isLt) (columnHeight_le mu _)]
    simp only [weight_indexCast]
    exact replacement_weight_difference _ _ x.1.property k
  have hs := Fintype.sum_of_injective (rootColumnEmbedding mu a hcapacity)
    (rootColumnEmbedding mu a hcapacity).injective
    (fun x : RootCopies a => (if k = x.1.val.2 then (1 : ℤ) else 0) - (if k = x.1.val.1 then 1 else 0))
    (fun c : Column mu => (weight (monomialBasis mu a hcapacity c) k : ℤ) -
      (weight (first (columnHeight_le mu c)) k : ℤ))
    (fun c hc => by
      dsimp only
      rw [monomialBasis_off mu a hcapacity c hc, sub_self]) (fun x => (hi x).symm)
  have hf : (mu k : ℤ) = ∑ c : Column mu, (weight (first (columnHeight_le mu c)) k : ℤ) := by
    have h := congrFun (tensorFirst_weight mu hmu) k
    exact_mod_cast h.symm
  rw [hf]
  change ((∑ c : Column mu, weight (monomialBasis mu a hcapacity c) k : ℕ) : ℤ) - _ = _
  rw [Nat.cast_sum, ← Finset.sum_sub_distrib, ← hs, Fintype.sum_sigma]
  unfold rootWeightShift
  apply Finset.sum_congr rfl
  intro r _
  change (∑ _ : Fin (a r), ((if k = r.val.2 then (1 : ℤ) else 0) -
    (if k = r.val.1 then 1 else 0))) = _
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

theorem shallowMonomialBasis_weight_difference (hmu : Antitone mu) (g : ℕ)
    (hgap : ∀ j : Fin d, ∀ hj : j.val + 1 < d, g + mu ⟨j.val + 1, hj⟩ ≤ mu j)
    (hdepth : rootDepth a ≤ g) (k : Fin d) :
    (tensorWeight (columnHeight mu) (shallowMonomialBasis mu a hmu g hgap hdepth) k : ℤ) - (mu k : ℤ) =
      rootWeightShift a k :=
  monomialBasis_weight_difference mu a hmu _ k

/-- All explicitly constructed monomial coordinates with the same root
offset have the same genuine ambient torus weight. -/
theorem shallowMonomialBasis_weight_eq (b : LowerRoot d →₀ ℕ) (hmu : Antitone mu) (g : ℕ)
    (hgap : ∀ j : Fin d, ∀ hj : j.val + 1 < d, g + mu ⟨j.val + 1, hj⟩ ≤ mu j)
    (ha : rootDepth a ≤ g) (hb : rootDepth b ≤ g)
    (hab : rootWeightShift a = rootWeightShift b) :
    tensorWeight (columnHeight mu) (shallowMonomialBasis mu a hmu g hgap ha) =
      tensorWeight (columnHeight mu) (shallowMonomialBasis mu b hmu g hgap hb) := by
  funext k
  have ha' := shallowMonomialBasis_weight_difference mu a hmu g hgap ha k
  have hb' := shallowMonomialBasis_weight_difference mu b hmu g hgap hb k
  have hk := congrFun hab k
  omega

end FreeEntropy.ExteriorRepresentation
