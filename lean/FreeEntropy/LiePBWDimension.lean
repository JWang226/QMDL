/-
Copyright (c) 2026 Free Entropy formalization contributors.
See LICENSE and NOTICE in the repository root for license and attribution.
-/

import FreeEntropy.LiePBWMultiplicity

/-! A polynomial dimension bound for genuine cyclic highest-weight modules
whose diagonal weights are nonnegative occupations of a fixed tensor degree.
Every nonzero ordered lowering word has bounded root depth; the finite
exponent box then spans the whole representation. -/
noncomputable section
open Matrix
open scoped BigOperators
namespace FreeEntropy.LiePBW
open LieMatrixCasimir ExteriorRepresentation
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
set_option linter.unusedSectionVars false
variable {d : ℕ} {H : Type*} [Fintype H] [DecidableEq H]

/-- Each individual positive-root coefficient is bounded by total root depth. -/
theorem rootCoefficient_le_depth (a : LowerRoot d →₀ ℕ) (r : LowerRoot d) :
    a r ≤ rootDepth a := by
  have hs : a r ≤ ∑ s : LowerRoot d, a s := Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ r)
  have hd := rootCopies_card_le_depth a
  rw [rootCopies_card] at hd
  exact hs.trans hd

/-- Nonzero lowering words in degree `n` have root depth at most `n(d−1)`. -/
theorem lowerWord_depth_le_of_ne_zero
    (R : Generators d H) (wt : H → Fin d → ℕ) (n : ℕ)
    (hdiag : ∀ k, R.E k k = diagonal (fun h => (wt h k : ℂ)))
    (hsum : ∀ h, ∑ k, wt h k = n)
    (lam : Fin d → ℕ) (v : H → ℂ)
    (hweight : ∀ k, R.E k k *ᵥ v = (lam k : ℂ) • v)
    (l : List (LowerRoot d)) (hne : lowerWord R l *ᵥ v ≠ 0) :
    rootDepth (lowerExponent l) ≤ n * (d - 1) := by
  classical
  obtain ⟨b, hb⟩ : ∃ b, (lowerWord R l *ᵥ v) b ≠ 0 := by
    by_contra hn
    push_neg at hn
    exact hne (funext hn)
  have he (k : Fin d) : (wt b k : ℤ) - (lam k : ℤ) = rootWeightShift (lowerExponent l) k := by
    have h := congrFun (lowerWord_weight R (fun k => (lam k : ℂ)) v hweight l k) b
    rw [hdiag, Matrix.mulVec_diagonal] at h
    change (wt b k : ℂ) * _ = ((lam k : ℂ) + (rootWeightShift (lowerExponent l) k : ℂ)) * _ at h
    have hc := mul_right_cancel₀ hb h
    have hc' : (wt b k : ℂ) - (lam k : ℂ) = (rootWeightShift (lowerExponent l) k : ℂ) := by
      linear_combination hc
    exact_mod_cast hc'
  have hd := rootDepth_eq_weightShift (lowerExponent l)
  simp_rw [← he] at hd
  have heq : (rootDepth (lowerExponent l) : ℤ) =
      (∑ k : Fin d, (k.val : ℤ) * (wt b k : ℤ)) - ∑ k : Fin d, (k.val : ℤ) * (lam k : ℤ) := by
    simpa only [mul_sub, Finset.sum_sub_distrib] using hd
  have hl : (0 : ℤ) ≤ ∑ k : Fin d, (k.val : ℤ) * (lam k : ℤ) :=
    Finset.sum_nonneg (fun k _ => mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
  have henergy : ∑ k : Fin d, k.val * wt b k ≤ n * (d - 1) := by
    calc
      _ ≤ ∑ k : Fin d, (d - 1) * wt b k := by
        apply Finset.sum_le_sum
        intro k _
        exact Nat.mul_le_mul_right _ (by omega)
      _ = (d - 1) * n := by rw [← Finset.mul_sum, hsum]
      _ = n * (d - 1) := Nat.mul_comm _ _
  have henergy' : (∑ k : Fin d, (k.val : ℤ) * (wt b k : ℤ)) ≤ (n * (d - 1) : ℕ) := by
    exact_mod_cast henergy
  exact_mod_cast (show (rootDepth (lowerExponent l) : ℤ) ≤ (n * (d - 1) : ℕ) by omega)

abbrev BoundedOrderedLoweringWord (d T : ℕ) :=
  {l : OrderedLoweringWord d // ∀ r, lowerExponent l.val r ≤ T}

def boundedOrderedWordEmbedding (T : ℕ) :
    BoundedOrderedLoweringWord d T ↪ (LowerRoot d → Fin (T + 1)) where
  toFun l r := ⟨lowerExponent l.val.val r, Nat.lt_succ_of_le (l.property r)⟩
  inj' := by
    intro l m h
    apply Subtype.ext
    apply lowerExponent_injective_on_ordered
    ext r
    exact congrArg Fin.val (congrFun h r)

noncomputable instance boundedOrderedWordFintype (T : ℕ) : Fintype (BoundedOrderedLoweringWord d T) :=
  Fintype.ofInjective (boundedOrderedWordEmbedding T) (boundedOrderedWordEmbedding T).injective

def boundedLoweringSpan (R : Generators d H) (v : H → ℂ) (T : ℕ) : Submodule ℂ (H → ℂ) :=
  Submodule.span ℂ (Set.range (fun l : BoundedOrderedLoweringWord d T => lowerWord R l.val.val *ᵥ v))

/-- The actual PBW span is contained in a polynomial-size exponent box. -/
theorem cyclicSpan_le_boundedLoweringSpan
    (R : Generators d H) (wt : H → Fin d → ℕ) (n : ℕ)
    (hdiag : ∀ k, R.E k k = diagonal (fun h => (wt h k : ℂ)))
    (hsum : ∀ h, ∑ k, wt h k = n)
    (lam : Fin d → ℕ) (v : H → ℂ)
    (hweight : ∀ k, R.E k k *ᵥ v = (lam k : ℂ) • v)
    (hraise : ∀ i j, i < j → R.E i j *ᵥ v = 0) :
    cyclicSpan R v ≤ boundedLoweringSpan R v (n * (d - 1)) := by
  classical
  rw [cyclicSpan_eq_orderedLoweringSpan R (fun k => (lam k : ℂ)) v hweight hraise]
  apply Submodule.span_le.mpr
  rintro _ ⟨l, rfl⟩
  change lowerWord R l.val *ᵥ v ∈ boundedLoweringSpan R v (n * (d - 1))
  by_cases hz : lowerWord R l.val *ᵥ v = 0
  · rw [hz]
    exact Submodule.zero_mem _
  · have hd := lowerWord_depth_le_of_ne_zero R wt n hdiag hsum lam v hweight l.val hz
    exact Submodule.subset_span ⟨⟨l, fun r => (rootCoefficient_le_depth _ r).trans hd⟩, rfl⟩

/-- A uniform polynomial bound on the actual cyclic module dimension. -/
theorem cyclicSpan_finrank_le_polynomial
    (R : Generators d H) (wt : H → Fin d → ℕ) (n : ℕ)
    (hdiag : ∀ k, R.E k k = diagonal (fun h => (wt h k : ℂ)))
    (hsum : ∀ h, ∑ k, wt h k = n)
    (lam : Fin d → ℕ) (v : H → ℂ)
    (hweight : ∀ k, R.E k k *ᵥ v = (lam k : ℂ) • v)
    (hraise : ∀ i j, i < j → R.E i j *ᵥ v = 0) :
    Module.finrank ℂ (cyclicSpan R v) ≤ (n * (d - 1) + 1) ^ (d.choose 2) := by
  calc
    _ ≤ Module.finrank ℂ (boundedLoweringSpan R v (n * (d - 1))) :=
      Submodule.finrank_mono (cyclicSpan_le_boundedLoweringSpan R wt n hdiag hsum lam v hweight hraise)
    _ ≤ Fintype.card (BoundedOrderedLoweringWord d (n * (d - 1))) := finrank_range_le_card _
    _ ≤ Fintype.card (LowerRoot d → Fin (n * (d - 1) + 1)) :=
      Fintype.card_le_of_embedding (boundedOrderedWordEmbedding _)
    _ = _ := by simp [Fintype.card_fun, card_lowerRoot]

/-- In a cyclic representation the same bound controls its literal matrix size. -/
theorem card_le_polynomial_of_cyclic
    (R : Generators d H) (wt : H → Fin d → ℕ) (n : ℕ)
    (hdiag : ∀ k, R.E k k = diagonal (fun h => (wt h k : ℂ)))
    (hsum : ∀ h, ∑ k, wt h k = n)
    (lam : Fin d → ℕ) (v : H → ℂ)
    (hweight : ∀ k, R.E k k *ᵥ v = (lam k : ℂ) • v)
    (hraise : ∀ i j, i < j → R.E i j *ᵥ v = 0)
    (hcyclic : cyclicSpan R v = ⊤) :
    Fintype.card H ≤ (n * (d - 1) + 1) ^ (d.choose 2) := by
  have h := cyclicSpan_finrank_le_polynomial R wt n hdiag hsum lam v hweight hraise
  have he : Module.finrank ℂ (cyclicSpan R v) = Fintype.card H := by
    calc
      _ = Module.finrank ℂ (⊤ : Submodule ℂ (H → ℂ)) :=
        congrArg (fun S : Submodule ℂ (H → ℂ) => Module.finrank ℂ S) hcyclic
      _ = _ := by simp
  exact he ▸ h

end FreeEntropy.LiePBW
