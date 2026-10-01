/-
Copyright (c) 2026 Free Entropy formalization contributors.
See LICENSE and NOTICE in the repository root for license and attribution.
-/

import FreeEntropy.GelfandTsetlin
import Mathlib.Data.Fintype.Sigma

/-!
# Branching of actual integral Gelfand–Tsetlin patterns

Removing the top row is an explicit equivalence with a finite disjoint union
of smaller patterns indexed by independent interlacing integer intervals.
Consequently their cardinalities satisfy the branching recurrence used in
the dimension formula. No counting identity is assumed.
-/

noncomputable section
open scoped BigOperators

namespace FreeEntropy.GTDimension

open GelfandTsetlin

/-- An interlacing penultimate row, with independent finite integer coordinates. -/
def InterlacingRow {n : ℕ} (μ : Fin (n + 1) → ℤ) :=
  (i : Fin n) → {z : ℤ // z ∈ Finset.Icc (μ i.succ) (μ i.castSucc)}

instance {n : ℕ} (μ : Fin (n + 1) → ℤ) : Fintype (InterlacingRow μ) :=
  inferInstanceAs (Fintype ((i : Fin n) → {z : ℤ // z ∈ Finset.Icc (μ i.succ) (μ i.castSucc)}))

def interlacingWeight {n : ℕ} {μ : Fin (n + 1) → ℤ} (ν : InterlacingRow μ) : Fin n → ℤ :=
  fun i => (ν i).val

theorem interlacingWeight_lower {n : ℕ} {μ : Fin (n + 1) → ℤ} (ν : InterlacingRow μ)
    (i : Fin n) : μ i.succ ≤ interlacingWeight ν i := (Finset.mem_Icc.mp (ν i).property).1

theorem interlacingWeight_upper {n : ℕ} {μ : Fin (n + 1) → ℤ} (ν : InterlacingRow μ)
    (i : Fin n) : interlacingWeight ν i ≤ μ i.castSucc := (Finset.mem_Icc.mp (ν i).property).2

theorem interlacingWeight_dominant {n : ℕ} {μ : Fin (n + 1) → ℤ}
    (hμ : Dominant μ) (ν : InterlacingRow μ) : Dominant (interlacingWeight ν) := by
  intro i j hij
  rcases lt_or_eq_of_le hij with hij | hij
  · exact (interlacingWeight_upper ν j).trans
      ((hμ (by change i.val + 1 ≤ j.val; exact hij)).trans (interlacingWeight_lower ν i))
  · rw [hij]

/-- The actual penultimate row of an ambient pattern. -/
def penultimate {n : ℕ} {μ : Fin (n + 1) → ℤ} (P : Pattern μ) : InterlacingRow μ :=
  fun j => ⟨P.entry (Fin.last n).castSucc j, Finset.mem_Icc.mpr ⟨by
    have h := P.lower (Fin.last n) j
    change P.entry (Fin.last (n + 1)) j.succ ≤ P.entry (Fin.last n).castSucc j at h
    rwa [P.top] at h,
    by
      have h := P.upper (Fin.last n) j
      change P.entry (Fin.last n).castSucc j ≤ P.entry (Fin.last (n + 1)) j.castSucc at h
      rwa [P.top] at h⟩⟩

/-- Delete the top row. -/
def truncate {n : ℕ} {μ : Fin (n + 1) → ℤ} (P : Pattern μ) :
    Pattern (interlacingWeight (penultimate P)) where
  entry i j := P.entry i.castSucc j
  top _ := rfl
  upper i j := P.upper i.castSucc j
  lower i j := P.lower i.castSucc j

/-- Reinsert the prescribed top row above a smaller pattern. -/
def extendArray {n : ℕ} (μ : Fin (n + 1) → ℤ) (ν : InterlacingRow μ)
    (P : Pattern (interlacingWeight ν)) : GelfandTsetlin.Array (n + 1) := fun i j =>
  if hi : i.val ≤ n then P.entry ⟨i.val, by omega⟩ j else μ (column j)

theorem extendArray_small {n : ℕ} (μ : Fin (n + 1) → ℤ) (ν : InterlacingRow μ)
    (P : Pattern (interlacingWeight ν)) (i : Fin (n + 2)) (hi : i.val ≤ n)
    (j : Fin i.val) : extendArray μ ν P i j = P.entry ⟨i.val, by omega⟩ j := by
  simp only [extendArray, dif_pos hi]

theorem extendArray_top {n : ℕ} (μ : Fin (n + 1) → ℤ) (ν : InterlacingRow μ)
    (P : Pattern (interlacingWeight ν)) (j : Fin (n + 1)) :
    extendArray μ ν P (Fin.last (n + 1)) j = μ j := by
  simp [extendArray, column]

def extend {n : ℕ} (μ : Fin (n + 1) → ℤ) (ν : InterlacingRow μ)
    (P : Pattern (interlacingWeight ν)) : Pattern μ where
  entry := extendArray μ ν P
  top := extendArray_top μ ν P
  upper i j := by
    by_cases hi : i.val < n
    · rw [extendArray_small μ ν P i.castSucc (Nat.le_of_lt hi),
        extendArray_small μ ν P i.succ hi]
      exact P.upper ⟨i.val, hi⟩ j
    · have he : i.val = n := by have h := i.isLt; omega
      obtain ⟨i, hi'⟩ := i
      dsimp only at he
      subst i
      change extendArray μ ν P (Fin.last n).castSucc j ≤
        extendArray μ ν P (Fin.last (n + 1)) j.castSucc
      rw [extendArray_small μ ν P _ (by exact le_rfl), extendArray_top]
      change P.entry (Fin.last n) j ≤ _
      rw [P.top]
      exact interlacingWeight_upper ν j
  lower i j := by
    by_cases hi : i.val < n
    · rw [extendArray_small μ ν P i.succ hi,
        extendArray_small μ ν P i.castSucc (Nat.le_of_lt hi)]
      exact P.lower ⟨i.val, hi⟩ j
    · have he : i.val = n := by have h := i.isLt; omega
      obtain ⟨i, hi'⟩ := i
      dsimp only at he
      subst i
      change extendArray μ ν P (Fin.last (n + 1)) j.succ ≤
        extendArray μ ν P (Fin.last n).castSucc j
      rw [extendArray_top, extendArray_small μ ν P _ (by exact le_rfl)]
      change _ ≤ P.entry (Fin.last n) j
      rw [P.top]
      exact interlacingWeight_lower ν j

theorem penultimate_extend {n : ℕ} (μ : Fin (n + 1) → ℤ) (ν : InterlacingRow μ)
    (P : Pattern (interlacingWeight ν)) : penultimate (extend μ ν P) = ν := by
  funext j
  apply Subtype.ext
  change extendArray μ ν P (Fin.last n).castSucc j = interlacingWeight ν j
  rw [extendArray_small μ ν P _ (by exact le_rfl)]
  exact P.top j

private theorem pattern_heq_of_entry_eq {n : ℕ} {μ ν : Fin n → ℤ} (h : μ = ν)
    {P : Pattern μ} {Q : Pattern ν} (he : P.entry = Q.entry) : HEq P Q := by
  subst ν
  exact heq_of_eq (Pattern.ext he)

/-- The actual branching equivalence, not an assumed cardinal recurrence. -/
def branchingEquiv {n : ℕ} (μ : Fin (n + 1) → ℤ) :
    Pattern μ ≃ (ν : InterlacingRow μ) × Pattern (interlacingWeight ν) where
  toFun P := ⟨penultimate P, truncate P⟩
  invFun Q := extend μ Q.1 Q.2
  left_inv P := by
    apply Pattern.ext
    funext i j
    by_cases hi : i.val ≤ n
    · exact extendArray_small μ (penultimate P) (truncate P) i hi j
    · have he : i.val = n + 1 := by have h := i.isLt; omega
      obtain ⟨i, hi'⟩ := i
      dsimp only at he
      subst i
      change extendArray μ (penultimate P) (truncate P) (Fin.last (n + 1)) j =
        P.entry (Fin.last (n + 1)) j
      rw [extendArray_top, P.top]
  right_inv Q := by
    apply Sigma.ext (penultimate_extend μ Q.1 Q.2)
    apply pattern_heq_of_entry_eq (congrArg interlacingWeight (penultimate_extend μ Q.1 Q.2))
    funext i j
    exact extendArray_small μ Q.1 Q.2 i.castSucc (Nat.le_of_lt_succ i.isLt) j

/-- Cardinal branching over the explicit product of interlacing integer intervals. -/
theorem card_branching {n : ℕ} (μ : Fin (n + 1) → ℤ) :
    Fintype.card (Pattern μ) =
      ∑ ν : InterlacingRow μ, Fintype.card (Pattern (interlacingWeight ν)) := by
  rw [Fintype.card_congr (branchingEquiv μ), Fintype.card_sigma]

/-- There is exactly one empty triangular pattern. -/
theorem card_zero (μ : Fin 0 → ℤ) : Fintype.card (Pattern μ) = 1 := by
  let P : Pattern μ :=
    { entry := fun _ _ => 0
      top := fun j => Fin.elim0 j
      upper := fun i => Fin.elim0 i
      lower := fun i => Fin.elim0 i }
  apply Fintype.card_eq_one_iff.mpr
  refine ⟨P, ?_⟩
  intro Q
  apply Pattern.ext
  funext i j
  have hi := i.isLt
  have hj := j.isLt
  omega

end FreeEntropy.GTDimension
