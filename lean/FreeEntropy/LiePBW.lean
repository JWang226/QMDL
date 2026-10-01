/-
Copyright (c) 2026 Free Entropy formalization contributors.
See LICENSE and NOTICE in the repository root for license and attribution.
-/

import FreeEntropy.LieMatrixCasimir
import Mathlib.Data.List.Sort

/-! PBW spanning for the actual matrix generators: adjacent transpositions
produce only shorter commutator words, and strong induction together with
verified list sorting gives ordered spanning words. -/

noncomputable section
open Matrix
namespace FreeEntropy.LiePBW
open LieMatrixCasimir
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

variable {d : ℕ} {H : Type*} [Fintype H] [DecidableEq H]

abbrev Root (d : ℕ) := Fin d × Fin d

def word (R : Generators d H) (w : List (Root d)) : Matrix H H ℂ :=
  (w.map (fun a => R.E a.1 a.2)).prod

@[simp] theorem word_nil (R : Generators d H) : word R [] = 1 := rfl
@[simp] theorem word_cons (R : Generators d H) (a : Root d) (w : List (Root d)) :
    word R (a :: w) = R.E a.1 a.2 * word R w := rfl
@[simp] theorem word_append (R : Generators d H) (w v : List (Root d)) :
    word R (w ++ v) = word R w * word R v := by simp [word]

/-- Any permutation changes a word by a linear combination of strictly
shorter words. The prefix is retained during permutation induction. -/
theorem perm_difference_mem (R : Generators d H) (S : Submodule ℂ (Matrix H H ℂ))
    (n : ℕ) (hshort : ∀ w, w.length < n → word R w ∈ S)
    {u v : List (Root d)} (huv : u.Perm v) (p : List (Root d))
    (hlen : p.length + u.length ≤ n) : word R (p ++ u) - word R (p ++ v) ∈ S := by
  induction huv generalizing p with
  | nil => simp
  | @cons a u v h ih =>
    have he := ih (p ++ [a]) (by
      simp only [List.length_append, List.length_cons, List.length_nil] at *
      omega)
    simpa only [List.append_assoc, List.singleton_append] using he
  | swap a b w =>
    have h1 : word R (p ++ [(b.1, a.2)] ++ w) ∈ S :=
      hshort _ (by
        simp only [List.length_append, List.length_cons, List.length_nil] at *
        omega)
    have h2 : word R (p ++ [(a.1, b.2)] ++ w) ∈ S :=
      hshort _ (by
        simp only [List.length_append, List.length_cons, List.length_nil] at *
        omega)
    have he : word R (p ++ b :: a :: w) - word R (p ++ a :: b :: w) =
        (if b.2 = a.1 then word R (p ++ [(b.1, a.2)] ++ w) else 0) -
        (if a.2 = b.1 then word R (p ++ [(a.1, b.2)] ++ w) else 0) := by
      have hc := congrArg (fun X : Matrix H H ℂ => word R p * X * word R w)
        (R.commutator b.1 b.2 a.1 a.2)
      simp only [Matrix.mul_sub, Matrix.sub_mul] at hc
      simp only [word_append, word_cons, word_nil, Matrix.mul_one]
      split_ifs at * <;> (try simp only [Matrix.mul_zero, Matrix.zero_mul] at *) <;>
        simpa only [Matrix.mul_assoc] using hc
    rw [he]
    exact S.sub_mem (by split_ifs; exact h1; exact S.zero_mem)
      (by split_ifs; exact h2; exact S.zero_mem)
  | @trans u v w huv hvw ihu ihv =>
    have hleft := ihu p hlen
    have hright := ihv p (by simpa only [← huv.length_eq] using hlen)
    have hadd := S.add_mem hleft hright
    convert hadd using 1 <;> abel

def orderedSpan (R : Generators d H) (key : Root d → ℕ) : Submodule ℂ (Matrix H H ℂ) :=
  Submodule.span ℂ {M | ∃ w : List (Root d), w.Pairwise (fun a b => key a ≤ key b) ∧ word R w = M}

/-- Actual PBW ordered spanning, for any chosen natural ordering of the
matrix generators. No abstract PBW theorem is assumed. -/
theorem word_mem_orderedSpan (R : Generators d H) (key : Root d → ℕ) (w : List (Root d)) :
    word R w ∈ orderedSpan R key := by
  generalize hn : w.length = n
  induction n using Nat.strong_induction_on generalizing w with
  | h n ih =>
    let sorted := w.mergeSort (fun a b => decide (key a ≤ key b))
    have hp : sorted.Perm w := List.mergeSort_perm w _
    have hs : sorted.Pairwise (fun a b => key a ≤ key b) := by
      simpa only [decide_eq_true_eq] using List.pairwise_mergeSort
        (le := fun a b => decide (key a ≤ key b))
        (fun a b c hab hbc => by simpa using le_trans (of_decide_eq_true hab) (of_decide_eq_true hbc))
        (fun a b => by simp only [Bool.or_eq_true, decide_eq_true_eq]; exact le_total _ _) w
    have hm : word R sorted ∈ orderedSpan R key := Submodule.subset_span ⟨sorted, hs, rfl⟩
    have hd := perm_difference_mem R (orderedSpan R key) n
      (fun v hv => ih v.length hv v rfl) hp [] (by simp only [List.length_nil, zero_add, hp.length_eq, hn]; exact le_rfl)
    simp only [List.nil_append] at hd
    have hsub := (orderedSpan R key).sub_mem hm hd
    convert hsub using 1 <;> abel

/-- Equality of the spans of all words and ordered words. -/
theorem span_words_eq_orderedSpan (R : Generators d H) (key : Root d → ℕ) :
    Submodule.span ℂ (Set.range (word R)) = orderedSpan R key := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨w, rfl⟩
    exact word_mem_orderedSpan R key w
  · apply Submodule.span_le.mpr
    rintro _ ⟨w, _, rfl⟩
    exact Submodule.subset_span ⟨w, rfl⟩

/-- Lowering, diagonal, then raising order. -/
def kind (a : Root d) : ℕ := if a.2 < a.1 then 0 else if a.1 = a.2 then 1 else 2

end FreeEntropy.LiePBW
