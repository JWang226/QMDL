/-
Copyright (c) 2026 Free Entropy formalization contributors.
See LICENSE and NOTICE in the repository root for license and attribution.
-/

import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Int.Interval
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.Linarith
import Lean.Elab.Tactic.Omega

/-!
# Integral Gelfand–Tsetlin patterns and multiplicity monotonicity

Rows have lengths `0, …, d`; the empty row makes successive row sums uniform.
We prove finiteness from the interlacing inequalities, construct the columnwise
translation by a dominant integral weight, and obtain the cardinal inequality
for patterns with a fixed offset from the top weight. Identifying these counts
with irreducible representation weight multiplicities is a separate theorem.
-/

namespace FreeEntropy.GelfandTsetlin

open scoped BigOperators

/-- All integer triangular arrays with `d` nonempty rows. -/
abbrev Array (d : ℕ) := (i : Fin (d + 1)) → Fin i.val → ℤ

/-- The column of an entry, considered as an index in the top row. -/
def column {d : ℕ} {i : Fin (d + 1)} (j : Fin i.val) : Fin d :=
  ⟨j.val, lt_of_lt_of_le j.isLt (Nat.le_of_lt_succ i.isLt)⟩

/-- The usual integer GT patterns, with no independent boundedness assumptions. -/
structure Pattern {d : ℕ} (μ : Fin d → ℤ) where
  entry : Array d
  top : ∀ j : Fin d, entry (Fin.last d) j = μ j
  upper : ∀ (i : Fin d) (j : Fin i.val),
    entry i.castSucc j ≤ entry i.succ j.castSucc
  lower : ∀ (i : Fin d) (j : Fin i.val),
    entry i.succ j.succ ≤ entry i.castSucc j

@[ext] theorem Pattern.ext {d : ℕ} {μ : Fin d → ℤ}
    {P Q : Pattern μ} (h : P.entry = Q.entry) : P = Q := by
  cases P
  cases Q
  cases h
  rfl

/-- A dominant integral weight is weakly decreasing along its columns. -/
def Dominant {d : ℕ} (ω : Fin d → ℤ) : Prop := Antitone ω

/-- Row sums, including the empty row. -/
def rowSum {d : ℕ} {μ : Fin d → ℤ} (P : Pattern μ) (i : Fin (d + 1)) : ℤ :=
  ∑ j, P.entry i j

/-- The GT weight is the vector of successive row-sum differences. -/
def weight {d : ℕ} {μ : Fin d → ℤ} (P : Pattern μ) (i : Fin d) : ℤ :=
  rowSum P i.succ - rowSum P i.castSucc

/-- Translation by the column of a dominant weight preserves interlacing. -/
def shift {d : ℕ} {μ ω : Fin d → ℤ} (hω : Dominant ω)
    (P : Pattern μ) : Pattern (μ + ω) where
  entry i j := P.entry i j + ω (column j)
  top j := by simpa [column] using congrArg (· + ω j) (P.top j)
  upper i j := by
    have hc : column (i := i.castSucc) j = column (i := i.succ) j.castSucc :=
      Fin.ext rfl
    exact add_le_add (P.upper i j) (le_of_eq (congrArg ω hc))
  lower i j := by
    have hc : column (i := i.castSucc) j ≤ column (i := i.succ) j.succ := by
      change j.val ≤ j.val + 1
      omega
    exact add_le_add (P.lower i j) (hω hc)

/-- The columnwise translation is injective, including when entries are negative. -/
theorem shift_injective {d : ℕ} {μ ω : Fin d → ℤ} (hω : Dominant ω) :
    Function.Injective (shift (μ := μ) hω) := by
  intro P Q h
  apply Pattern.ext
  funext i j
  have hentry := congrArg (fun R => R.entry i j) h
  exact add_right_cancel hentry

theorem rowSum_shift {d : ℕ} {μ ω : Fin d → ℤ} (hω : Dominant ω)
    (P : Pattern μ) (i : Fin (d + 1)) :
    rowSum (shift hω P) i = rowSum P i + ∑ j : Fin i.val, ω (column j) := by
  simp [rowSum, shift, Finset.sum_add_distrib]

/-- Successive row-sum differences shift by exactly `ω`. -/
theorem weight_shift {d : ℕ} {μ ω : Fin d → ℤ} (hω : Dominant ω)
    (P : Pattern μ) : weight (shift hω P) = weight P + ω := by
  funext i
  simp only [weight, rowSum_shift, Pi.add_apply]
  have hs : (∑ j : Fin (i.val + 1), ω (column (i := i.succ) j)) =
      (∑ j : Fin i.val, ω (column (i := i.castSucc) j)) + ω i := by
    rw [Fin.sum_univ_castSucc]
    rfl
  change (rowSum P i.succ + ∑ j : Fin (i.val + 1), ω (column (i := i.succ) j)) -
      (rowSum P i.castSucc + ∑ j : Fin i.val, ω (column (i := i.castSucc) j)) = _
  rw [hs]
  omega

/-- Every entry lies between any lower and upper bounds for the top row. -/
theorem entry_bounds {d : ℕ} {μ : Fin d → ℤ} (P : Pattern μ)
    {L U : ℤ} (hμ : ∀ j, L ≤ μ j ∧ μ j ≤ U)
    (i : Fin (d + 1)) (j : Fin i.val) :
    L ≤ P.entry i j ∧ P.entry i j ≤ U := by
  have hrows : ∀ (r : ℕ) (hr : r ≤ d) (j : Fin r),
      L ≤ P.entry ⟨r, Nat.lt_succ_of_le hr⟩ j ∧
      P.entry ⟨r, Nat.lt_succ_of_le hr⟩ j ≤ U := by
    intro r hr
    induction hr using Nat.decreasingInduction with
    | self =>
      intro j
      change L ≤ P.entry (Fin.last d) j ∧ P.entry (Fin.last d) j ≤ U
      simpa only [P.top] using hμ j
    | @of_succ r hr ih =>
      intro j
      exact ⟨(ih j.succ).1.trans (P.lower ⟨r, hr⟩ j),
        (P.upper ⟨r, hr⟩ j).trans (ih j.castSucc).2⟩
  exact hrows i.val (Nat.le_of_lt_succ i.isLt) j

/-- A convenient finite bound, valid also for arbitrary negative integral top rows. -/
def topBound {d : ℕ} (μ : Fin d → ℤ) : ℤ := ∑ j, |μ j|

theorem entry_mem_Icc {d : ℕ} {μ : Fin d → ℤ} (P : Pattern μ)
    (i : Fin (d + 1)) (j : Fin i.val) :
    P.entry i j ∈ Finset.Icc (-topBound μ) (topBound μ) := by
  apply Finset.mem_Icc.mpr
  apply entry_bounds P
  intro k
  have habs : |μ k| ≤ topBound μ :=
    Finset.single_le_sum (fun l _ => abs_nonneg (μ l)) (Finset.mem_univ k)
  exact ⟨(neg_le_neg habs).trans (neg_abs_le (μ k)),
    (le_abs_self (μ k)).trans habs⟩

/-- Patterns are finite because their entries inhabit an explicitly bounded integer box. -/
noncomputable instance {d : ℕ} (μ : Fin d → ℤ) : Fintype (Pattern μ) := by
  classical
  let encode : Pattern μ → ((i : Fin (d + 1)) → Fin i.val →
      {z : ℤ // z ∈ Finset.Icc (-topBound μ) (topBound μ)}) :=
    fun P i j => ⟨P.entry i j, entry_mem_Icc P i j⟩
  apply Fintype.ofInjective encode
  intro P Q h
  apply Pattern.ext
  funext i j
  exact congrArg (fun a => (a i j).val) h

/-- Patterns at the fixed offset `δ` from their highest weight. -/
def OffsetPatterns {d : ℕ} (μ δ : Fin d → ℤ) :=
  {P : Pattern μ // weight P = μ - δ}

noncomputable instance {d : ℕ} (μ δ : Fin d → ℤ) : Fintype (OffsetPatterns μ δ) := by
  classical
  exact inferInstanceAs (Fintype {P : Pattern μ // weight P = μ - δ})

/-- The offset is unchanged by columnwise translation. -/
def shiftOffset {d : ℕ} {μ ω : Fin d → ℤ} (hω : Dominant ω)
    (δ : Fin d → ℤ) : OffsetPatterns μ δ → OffsetPatterns (μ + ω) δ :=
  fun P => ⟨shift hω P.val, by
    rw [weight_shift, P.property]
    funext i
    simp only [Pi.add_apply, Pi.sub_apply]
    omega⟩

theorem shiftOffset_injective {d : ℕ} {μ ω : Fin d → ℤ} (hω : Dominant ω)
    (δ : Fin d → ℤ) : Function.Injective (shiftOffset (μ := μ) hω δ) := by
  intro P Q h
  apply Subtype.ext
  exact shift_injective hω (congrArg Subtype.val h)

/-- The actual integer-pattern count at a highest-weight offset. -/
noncomputable def multiplicity {d : ℕ} (μ δ : Fin d → ℤ) : ℕ :=
  Fintype.card (OffsetPatterns μ δ)

/-- GT multiplicity monotonicity, proved by the explicit injective translation.

The statement holds for every integral offset, so in particular for `δ ∈ Q₊`.
The old top row need not be separately assumed dominant: if it has patterns,
its dominance follows from interlacing.
-/
theorem multiplicity_mono {d : ℕ} {μ ω : Fin d → ℤ} (hω : Dominant ω)
    (δ : Fin d → ℤ) : multiplicity μ δ ≤ multiplicity (μ + ω) δ :=
  Fintype.card_le_of_injective (shiftOffset hω δ) (shiftOffset_injective hω δ)

end FreeEntropy.GelfandTsetlin
