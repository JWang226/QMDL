/-
Copyright (c) 2026 Free Entropy formalization contributors.
See LICENSE and NOTICE in the repository root for license and attribution.
-/

import FreeEntropy.WordTypes

/-!
# Standard tableaux inject into words of the same content

Tableaux are actual bijective fillings of the Young-diagram cells, with
strict rows and columns. The row containing each label is a word of the
prescribed content. Strict row order makes that encoding injective.
-/
noncomputable section
open scoped BigOperators
namespace FreeEntropy.SchurProbabilityTableaux
open WordTypes
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
attribute [local instance] Classical.propDecidable

variable {r n : ℕ}

/-- A standard tableau as a bijective filling, with both order conditions. -/
structure StandardTableau (lam : Fin r → ℕ) (n : ℕ) where
  entry : (Σ i : Fin r, Fin (lam i)) ≃ Fin n
  row_strict : ∀ i, StrictMono (fun j : Fin (lam i) => entry ⟨i, j⟩)
  column_strict : ∀ (i k : Fin r), i < k → ∀ (j : Fin (lam i)) (l : Fin (lam k)),
    j.val = l.val → entry ⟨i, j⟩ < entry ⟨k, l⟩

@[ext] theorem StandardTableau.ext {lam : Fin r → ℕ} {T U : StandardTableau lam n}
    (h : T.entry = U.entry) : T = U := by
  cases T
  cases U
  cases h
  rfl

instance (lam : Fin r → ℕ) : Fintype (StandardTableau lam n) :=
  Fintype.ofInjective StandardTableau.entry (fun _ _ h => StandardTableau.ext h)

def rowWord {lam : Fin r → ℕ} (T : StandardTableau lam n) (t : Fin n) : Fin r :=
  (T.entry.symm t).fst

theorem range_entry_row {lam : Fin r → ℕ} (T : StandardTableau lam n) (i : Fin r) :
    Set.range (fun j : Fin (lam i) => T.entry ⟨i, j⟩) = {t | rowWord T t = i} := by
  ext t
  constructor
  · rintro ⟨j, rfl⟩
    simp [rowWord]
  · intro ht
    rcases hcell : T.entry.symm t with ⟨k, j⟩
    have hk : k = i := by simpa only [Set.mem_setOf_eq, rowWord, hcell] using ht
    subst k
    refine ⟨j, ?_⟩
    have h := T.entry.apply_symm_apply t
    rw [hcell] at h
    exact h

theorem rowWord_injective {lam : Fin r → ℕ} :
    Function.Injective (rowWord (lam := lam) (n := n)) := by
  intro T U he
  apply StandardTableau.ext
  apply Equiv.ext
  rintro ⟨i, j⟩
  have hr : Set.range (fun j : Fin (lam i) => T.entry ⟨i, j⟩) =
      Set.range (fun j : Fin (lam i) => U.entry ⟨i, j⟩) := by
    rw [range_entry_row, range_entry_row, he]
  exact congrFun (((T.row_strict i).range_inj (U.row_strict i)).mp hr) j

theorem rowWord_content {lam : Fin r → ℕ} (T : StandardTableau lam n) : content (rowWord T) = lam := by
  funext i
  have hf : Finset.univ.filter (fun t => rowWord T t = i) =
      Finset.univ.image (fun j : Fin (lam i) => T.entry ⟨i, j⟩) := by
    ext t
    constructor
    · intro ht
      have hr : t ∈ Set.range (fun j : Fin (lam i) => T.entry ⟨i, j⟩) := by
        rw [range_entry_row]
        exact (Finset.mem_filter.mp ht).2
      obtain ⟨j, hj⟩ := hr
      exact Finset.mem_image.mpr ⟨j, Finset.mem_univ _, hj⟩
    · intro ht
      obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp ht
      simp [rowWord]
  have hi : Function.Injective (fun j : Fin (lam i) => T.entry ⟨i, j⟩) := by
    intro j k h
    exact Sigma.mk.inj_iff.mp (T.entry.injective h) |>.2 |> eq_of_heq
  rw [content, hf, Finset.card_image_of_injective _ hi, Finset.card_univ, Fintype.card_fin]

/-- The genuine row-word encoding into the prescribed type class. -/
def toWords {lam : Fin r → ℕ} (T : StandardTableau lam n) : Words (n := n) lam :=
  ⟨rowWord T, rowWord_content T⟩

theorem toWords_injective {lam : Fin r → ℕ} :
    Function.Injective (toWords (lam := lam) (n := n)) := by
  intro T U h
  exact rowWord_injective (congrArg Subtype.val h)

/-- Standard-tableau multiplicity is bounded by the actual type-class count. -/
theorem tableau_card_le_words (lam : Fin r → ℕ) :
    Fintype.card (StandardTableau lam n) ≤ Fintype.card (Words (n := n) lam) :=
  Fintype.card_le_of_injective toWords toWords_injective

/-- Standard tableaux times the highest monomial obey the entropy bound;
no abstract multiplicity or pointwise probability estimate is assumed. -/
theorem tableau_monomial_le_exp_neg_kl (lam : Fin r → ℕ) (hn : 0 < n)
    (hsize : ∑ i, lam i = n) (x : Fin r → ℝ) (hx : ∀ i, 0 < x i) :
    (Fintype.card (StandardTableau lam n) : ℝ) * monomial lam x ≤
      Real.exp (-(n : ℝ) * FiniteConcentration.kl (empirical lam n) x) := by
  have hc : (Fintype.card (StandardTableau lam n) : ℝ) ≤ Fintype.card (Words (n := n) lam) :=
    by exact_mod_cast tableau_card_le_words (n := n) lam
  exact (mul_le_mul_of_nonneg_right hc (Finset.prod_nonneg (fun i _ => pow_nonneg (hx i).le _))).trans
    (type_probability_le_exp_neg_kl lam hn hsize x hx)

end FreeEntropy.SchurProbabilityTableaux
