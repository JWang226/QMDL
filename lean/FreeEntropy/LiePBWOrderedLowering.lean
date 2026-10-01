/-
Copyright (c) 2026 Free Entropy formalization contributors.
See LICENSE and NOTICE in the repository root for license and attribution.
-/

import FreeEntropy.LiePBWHighest
import FreeEntropy.ExteriorRootCounting
import Mathlib.Data.Finsupp.Multiset

/-! PBW with a genuine total order on lowering generators. Sorted lowering
words are uniquely encoded by their actual root-occurrence assignments. -/
noncomputable section
open Matrix
open scoped BigOperators
namespace FreeEntropy.LiePBW
open LieMatrixCasimir ExteriorRepresentation
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
set_option linter.unusedSectionVars false
variable {d : ℕ} {H : Type*} [Fintype H] [DecidableEq H]

def fullKey (a : Root d) : ℕ :=
  if a.2 < a.1 then (Fintype.equivFin (Root d) a).val
  else Fintype.card (Root d) + (Fintype.equivFin (Root d) a).val

theorem fullKey_injective : Function.Injective (fullKey (d := d)) := by
  intro a b hab
  have ha := (Fintype.equivFin (Root d) a).isLt
  have hb := (Fintype.equivFin (Root d) b).isLt
  apply (Fintype.equivFin (Root d)).injective
  apply Fin.ext
  unfold fullKey at hab
  split_ifs at hab <;> omega

theorem lower_of_fullKey_le {a b : Root d} (hab : fullKey a ≤ fullKey b) (hb : b.2 < b.1) :
    a.2 < a.1 := by
  by_contra ha
  have hb' := (Fintype.equivFin (Root d) b).isLt
  simp only [fullKey, if_pos hb, if_neg ha] at hab
  omega

/-- Ordered words retain a sorted lowering prefix after acting on a highest vector. -/
theorem fully_ordered_word_scalar_lowering
    (R : Generators d H) (lam : Fin d → ℂ) (v : H → ℂ)
    (hweight : ∀ i, R.E i i *ᵥ v = lam i • v)
    (hraise : ∀ i j, i < j → R.E i j *ᵥ v = 0)
    (w : List (Root d)) (hw : w.Pairwise (fun a b => fullKey a ≤ fullKey b)) :
    ∃ l : List (Root d), (∀ a ∈ l, a.2 < a.1) ∧ l.Sublist w ∧
      ∃ c : ℂ, word R w *ᵥ v = c • (word R l *ᵥ v) := by
  induction w with
  | nil => exact ⟨[], by simp, by simp, 1, by simp⟩
  | cons a w ih =>
    obtain ⟨hab, htail⟩ := List.pairwise_cons.mp hw
    by_cases ha : a.2 < a.1
    · obtain ⟨l, hl, hsub, c, hc⟩ := ih htail
      refine ⟨a :: l, ?_, hsub.cons_cons a, c, ?_⟩
      · intro b hb
        rcases List.mem_cons.mp hb with rfl | hb
        · exact ha
        · exact hl b hb
      · simp only [word_cons, ← Matrix.mulVec_mulVec, hc, Matrix.mulVec_smul]
    · have hn : ∀ b ∈ a :: w, ¬ b.2 < b.1 := by
        intro b hb
        rcases List.mem_cons.mp hb with rfl | hb
        · exact ha
        · exact fun hbl => ha (lower_of_fullKey_le (hab b hb) hbl)
      obtain ⟨c, hc⟩ := nonlower_word_scalar R lam v hweight hraise (a :: w) hn
      exact ⟨[], by simp, by simp, c, by simpa only [word_nil, Matrix.one_mulVec] using hc⟩

def loweringRoot (r : LowerRoot d) : Root d := (r.val.2, r.val.1)

def loweringList (w : List (Root d)) (hw : ∀ a ∈ w, a.2 < a.1) : List (LowerRoot d) :=
  w.pmap (fun a h => (⟨(a.2, a.1), h⟩ : LowerRoot d)) hw

theorem loweringList_map (w : List (Root d)) (hw : ∀ a ∈ w, a.2 < a.1) :
    (loweringList w hw).map loweringRoot = w := by
  induction w with
  | nil => rfl
  | cons a w ih =>
    simp only [loweringList, List.pmap_cons, List.map_cons]
    congr 1
    exact ih _

abbrev OrderedLoweringWord (d : ℕ) :=
  {l : List (LowerRoot d) // l.Pairwise (fun a b => fullKey (loweringRoot a) ≤ fullKey (loweringRoot b))}

def lowerExponent (l : List (LowerRoot d)) : LowerRoot d →₀ ℕ :=
  (l : Multiset (LowerRoot d)).toFinsupp

theorem lowerExponent_injective_on_ordered :
    Function.Injective (fun l : OrderedLoweringWord d => lowerExponent l.val) := by
  intro a b he
  apply Subtype.ext
  have hp : a.val.Perm b.val := Multiset.coe_eq_coe.mp (Multiset.toFinsupp.injective he)
  apply List.Perm.eq_of_pairwise ?_ a.property b.property hp
  intro x y _ _ hxy hyx
  have hroot := fullKey_injective (le_antisymm hxy hyx)
  apply Subtype.ext
  exact Prod.ext (congrArg Prod.snd hroot) (congrArg Prod.fst hroot)

def lowerWord (R : Generators d H) (l : List (LowerRoot d)) : Matrix H H ℂ :=
  word R (l.map loweringRoot)

def orderedLoweringSpan (R : Generators d H) (v : H → ℂ) : Submodule ℂ (H → ℂ) :=
  Submodule.span ℂ (Set.range (fun l : OrderedLoweringWord d => lowerWord R l.val *ᵥ v))

theorem word_action_mem_orderedLoweringSpan
    (R : Generators d H) (lam : Fin d → ℂ) (v : H → ℂ)
    (hweight : ∀ i, R.E i i *ᵥ v = lam i • v)
    (hraise : ∀ i j, i < j → R.E i j *ᵥ v = 0) (w : List (Root d)) :
    word R w *ᵥ v ∈ orderedLoweringSpan R v := by
  have hm := word_mem_orderedSpan R fullKey w
  generalize he : word R w = M at hm ⊢
  clear he w
  change M ∈ Submodule.span ℂ _ at hm
  induction hm using Submodule.span_induction with
  | mem M hM =>
    obtain ⟨t, ht, rfl⟩ := hM
    obtain ⟨l, hl, hsub, c, hc⟩ := fully_ordered_word_scalar_lowering R lam v hweight hraise t ht
    rw [hc]
    apply (orderedLoweringSpan R v).smul_mem c
    have hs : (loweringList l hl).Pairwise
        (fun a b => fullKey (loweringRoot a) ≤ fullKey (loweringRoot b)) := by
      apply (List.pairwise_map (f := loweringRoot)
        (R := fun a b : Root d => fullKey a ≤ fullKey b)).mp
      rw [loweringList_map]
      exact ht.sublist hsub
    apply Submodule.subset_span
    refine ⟨⟨loweringList l hl, hs⟩, ?_⟩
    simp only [lowerWord, loweringList_map]
  | zero => simp
  | add M N hM hN ihM ihN =>
    simpa only [Matrix.add_mulVec] using (orderedLoweringSpan R v).add_mem ihM ihN
  | smul c M hM ihM =>
    simpa only [Matrix.smul_mulVec] using (orderedLoweringSpan R v).smul_mem c ihM

theorem cyclicSpan_eq_orderedLoweringSpan
    (R : Generators d H) (lam : Fin d → ℂ) (v : H → ℂ)
    (hweight : ∀ i, R.E i i *ᵥ v = lam i • v)
    (hraise : ∀ i j, i < j → R.E i j *ᵥ v = 0) :
    cyclicSpan R v = orderedLoweringSpan R v := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨w, rfl⟩
    exact word_action_mem_orderedLoweringSpan R lam v hweight hraise w
  · apply Submodule.span_le.mpr
    rintro _ ⟨l, rfl⟩
    exact Submodule.subset_span ⟨l.val.map loweringRoot, rfl⟩

end FreeEntropy.LiePBW
