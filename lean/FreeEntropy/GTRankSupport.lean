/-
Copyright (c) 2026 Free Entropy formalization contributors.
See LICENSE and NOTICE in the repository root for license and attribution.
-/

import FreeEntropy.GTPartitions

/-!
# Rank support for integral GT patterns

For a nonnegative dominant top row with zero entries after rank `r`,
patterns whose weights vanish after rank `r` are equivalent to rank-`r`
patterns. This is a statement about the actual integer arrays and weights,
independent of the theorem identifying GT counts with representations.
-/

noncomputable section
open scoped BigOperators

namespace FreeEntropy.GelfandTsetlin

theorem entry_nonneg {d : ℕ} {μ : Fin d → ℤ} (P : Pattern μ)
    (hμ : ∀ j, 0 ≤ μ j) (i : Fin (d + 1)) (j : Fin i.val) :
    0 ≤ P.entry i j := by
  apply (entry_bounds P (L := 0) (U := topBound μ) ?_ i j).1
  intro k
  exact ⟨hμ k, (le_abs_self (μ k)).trans
    (Finset.single_le_sum (fun l _ => abs_nonneg (μ l)) (Finset.mem_univ k))⟩

/-- A zero weight component forces every vertical drop in that row to be zero. -/
theorem entry_eq_above_of_weight_zero {d : ℕ} {μ : Fin d → ℤ} (P : Pattern μ)
    (hμ : ∀ j, 0 ≤ μ j) (i : Fin d) (hw : weight P i = 0)
    (j : Fin i.val) : P.entry i.castSucc j = P.entry i.succ j.castSucc := by
  have hsum := hw
  unfold weight rowSum at hsum
  change (∑ k : Fin (i.val + 1), P.entry i.succ k) -
    (∑ k : Fin i.val, P.entry i.castSucc k) = 0 at hsum
  rw [Fin.sum_univ_castSucc] at hsum
  have hu : (∑ k : Fin i.val, P.entry i.castSucc k) ≤
      ∑ k : Fin i.val, P.entry i.succ k.castSucc :=
    Finset.sum_le_sum (fun k _ => P.upper i k)
  have hn := entry_nonneg P hμ i.succ (Fin.last i.val)
  have he : (∑ k : Fin i.val, P.entry i.castSucc k) =
      ∑ k : Fin i.val, P.entry i.succ k.castSucc := by omega
  exact (Finset.sum_eq_sum_iff_of_le (fun k _ => P.upper i k)).mp he j (Finset.mem_univ j)

/-- Vanishing trailing weight components force every row above the rank to equal the top row. -/
theorem supported_upper_rows {d r : ℕ} {μ : Fin d → ℤ} (P : Pattern μ)
    (hμ : ∀ j, 0 ≤ μ j) (hw : ∀ i : Fin d, r ≤ i.val → weight P i = 0)
    (i : Fin (d + 1)) (hi : r ≤ i.val) (j : Fin i.val) :
    P.entry i j = μ (column j) := by
  have hrows : ∀ (k : ℕ) (hk : k ≤ d), r ≤ k → ∀ j : Fin k,
      P.entry ⟨k, Nat.lt_succ_of_le hk⟩ j =
        μ (column (i := ⟨k, Nat.lt_succ_of_le hk⟩) j) := by
    intro k hk
    induction hk using Nat.decreasingInduction with
    | self =>
      intro _ j
      simpa [column] using P.top j
    | @of_succ k hk ih =>
      intro hr j
      have he := entry_eq_above_of_weight_zero P hμ ⟨k, hk⟩ (hw ⟨k, hk⟩ hr) j
      exact he.trans (ih (by omega) j.castSucc)
  exact hrows i.val (Nat.le_of_lt_succ i.isLt) hi j

/-- Restriction of a top row (or a weight) to its first `r` coordinates. -/
def restrictRow {d r : ℕ} (hrd : r ≤ d) (μ : Fin d → ℤ) : Fin r → ℤ :=
  fun j => μ (j.castLE hrd)

/-- Actual ambient GT patterns with weight supported in the first `r` coordinates. -/
def SupportedPatterns {d : ℕ} (μ : Fin d → ℤ) (r : ℕ) :=
  {P : Pattern μ // ∀ i : Fin d, r ≤ i.val → weight P i = 0}

instance {d : ℕ} (μ : Fin d → ℤ) (r : ℕ) : Fintype (SupportedPatterns μ r) := by
  classical
  exact inferInstanceAs (Fintype {P : Pattern μ // ∀ i : Fin d, r ≤ i.val → weight P i = 0})

/-- Restriction to the first `r` rows, whose top is forced by weight support. -/
def restrictPattern {d r : ℕ} {μ : Fin d → ℤ} (hrd : r ≤ d)
    (hμ : ∀ j, 0 ≤ μ j) (P : SupportedPatterns μ r) : Pattern (restrictRow hrd μ) where
  entry i j := P.val.entry ⟨i.val, by have hi := i.isLt; omega⟩ j
  top j := supported_upper_rows P.val hμ P.property ⟨r, by omega⟩ le_rfl j
  upper i j := P.val.upper (i.castLE hrd) j
  lower i j := P.val.lower (i.castLE hrd) j

theorem weight_restrictPattern {d r : ℕ} {μ : Fin d → ℤ} (hrd : r ≤ d)
    (hμ : ∀ j, 0 ≤ μ j) (P : SupportedPatterns μ r) (i : Fin r) :
    weight (restrictPattern hrd hμ P) i = weight P.val (i.castLE hrd) := rfl

/-- Extend a rank-`r` array by the forced constant upper rows. -/
def padArray {d r : ℕ} {μ : Fin d → ℤ} (hrd : r ≤ d)
    (P : Pattern (restrictRow hrd μ)) : Array d := fun i j =>
  if hi : i.val ≤ r then P.entry ⟨i.val, by omega⟩ j else μ (column j)

theorem padArray_small {d r : ℕ} {μ : Fin d → ℤ} (hrd : r ≤ d)
    (P : Pattern (restrictRow hrd μ)) (i : Fin (d + 1)) (hi : i.val ≤ r)
    (j : Fin i.val) : padArray hrd P i j = P.entry ⟨i.val, by omega⟩ j := by
  simp only [padArray, dif_pos hi]

theorem padArray_large {d r : ℕ} {μ : Fin d → ℤ} (hrd : r ≤ d)
    (P : Pattern (restrictRow hrd μ)) (i : Fin (d + 1)) (hi : r ≤ i.val)
    (j : Fin i.val) : padArray hrd P i j = μ (column j) := by
  by_cases hir : i.val ≤ r
  · have he : i.val = r := by omega
    obtain ⟨i, hi'⟩ := i
    dsimp only at he
    subst i
    simpa [padArray, restrictRow, column] using P.top j
  · simp only [padArray, dif_neg hir]

/-- Padding is an actual GT pattern: all extra interlacing follows from dominance. -/
def padPattern {d r : ℕ} {μ : Fin d → ℤ} (hrd : r ≤ d) (hμ : Dominant μ)
    (P : Pattern (restrictRow hrd μ)) : Pattern μ where
  entry := padArray hrd P
  top j := by simpa [column] using padArray_large hrd P (Fin.last d) hrd j
  upper i j := by
    by_cases hi : i.val < r
    · rw [padArray_small hrd P i.castSucc (by exact Nat.le_of_lt hi),
        padArray_small hrd P i.succ (by exact hi)]
      exact P.upper ⟨i.val, hi⟩ j
    · rw [padArray_large hrd P i.castSucc (by change r ≤ i.val; omega),
        padArray_large hrd P i.succ (by change r ≤ i.val + 1; omega)]
      rfl
  lower i j := by
    by_cases hi : i.val < r
    · rw [padArray_small hrd P i.succ (by exact hi),
        padArray_small hrd P i.castSucc (by exact Nat.le_of_lt hi)]
      exact P.lower ⟨i.val, hi⟩ j
    · rw [padArray_large hrd P i.succ (by change r ≤ i.val + 1; omega),
        padArray_large hrd P i.castSucc (by change r ≤ i.val; omega)]
      exact hμ (by change j.val ≤ j.val + 1; omega)

theorem padPattern_entry_small {d r : ℕ} {μ : Fin d → ℤ} (hrd : r ≤ d)
    (hμ : Dominant μ) (P : Pattern (restrictRow hrd μ))
    (i : Fin (d + 1)) (hi : i.val ≤ r) (j : Fin i.val) :
    (padPattern hrd hμ P).entry i j = P.entry ⟨i.val, by omega⟩ j :=
  padArray_small hrd P i hi j

theorem padPattern_entry_large {d r : ℕ} {μ : Fin d → ℤ} (hrd : r ≤ d)
    (hμ : Dominant μ) (P : Pattern (restrictRow hrd μ))
    (i : Fin (d + 1)) (hi : r ≤ i.val) (j : Fin i.val) :
    (padPattern hrd hμ P).entry i j = μ (column j) :=
  padArray_large hrd P i hi j

theorem weight_padPattern_low {d r : ℕ} {μ : Fin d → ℤ} (hrd : r ≤ d)
    (hμ : Dominant μ) (P : Pattern (restrictRow hrd μ)) (i : Fin r) :
    weight (padPattern hrd hμ P) (i.castLE hrd) = weight P i := by
  unfold weight rowSum
  congr 1 <;> apply Finset.sum_congr rfl <;> intro j _
  · exact padPattern_entry_small hrd hμ P _ (by exact i.isLt) j
  · exact padPattern_entry_small hrd hμ P _ (Nat.le_of_lt i.isLt) j

theorem weight_padPattern_high {d r : ℕ} {μ : Fin d → ℤ} (hrd : r ≤ d)
    (hμ : Dominant μ) (P : Pattern (restrictRow hrd μ))
    (i : Fin d) (hi : r ≤ i.val) : weight (padPattern hrd hμ P) i = μ i := by
  unfold weight rowSum
  have hsucc : (∑ j, (padPattern hrd hμ P).entry i.succ j) =
      ∑ j : Fin (i.val + 1), μ (column (i := i.succ) j) := by
    apply Finset.sum_congr rfl
    intro j _
    exact padPattern_entry_large hrd hμ P i.succ (by change r ≤ i.val + 1; omega) j
  have hcast : (∑ j, (padPattern hrd hμ P).entry i.castSucc j) =
      ∑ j : Fin i.val, μ (column (i := i.castSucc) j) := by
    apply Finset.sum_congr rfl
    intro j _
    exact padPattern_entry_large hrd hμ P i.castSucc hi j
  rw [hsucc, hcast, Fin.sum_univ_castSucc]
  change ((∑ j : Fin i.val, μ (column (i := i.castSucc) j)) + μ i) - _ = _
  omega

/-- Padding gives a supported ambient pattern when the added top coordinates are zero. -/
def padSupported {d r : ℕ} {μ : Fin d → ℤ} (hrd : r ≤ d) (hμ : Dominant μ)
    (hzero : ∀ i : Fin d, r ≤ i.val → μ i = 0)
    (P : Pattern (restrictRow hrd μ)) : SupportedPatterns μ r :=
  ⟨padPattern hrd hμ P, fun i hi => (weight_padPattern_high hrd hμ P i hi).trans (hzero i hi)⟩

/-- The concrete rank-support equivalence, by restriction and forced-row padding. -/
def rankSupportEquiv {d r : ℕ} {μ : Fin d → ℤ} (hrd : r ≤ d)
    (hμ : Dominant μ) (hnonneg : ∀ j, 0 ≤ μ j)
    (hzero : ∀ i : Fin d, r ≤ i.val → μ i = 0) :
    SupportedPatterns μ r ≃ Pattern (restrictRow hrd μ) where
  toFun := restrictPattern hrd hnonneg
  invFun := padSupported hrd hμ hzero
  left_inv P := by
    apply Subtype.ext
    apply Pattern.ext
    funext i j
    by_cases hi : i.val ≤ r
    · exact padPattern_entry_small hrd hμ (restrictPattern hrd hnonneg P) i hi j
    · have hi' : r ≤ i.val := by omega
      exact (padPattern_entry_large hrd hμ (restrictPattern hrd hnonneg P) i hi' j).trans
        (supported_upper_rows P.val hnonneg P.property i hi' j).symm
  right_inv P := by
    apply Pattern.ext
    funext i j
    exact padPattern_entry_small hrd hμ P ⟨i.val, by have hi := i.isLt; omega⟩
      (Nat.le_of_lt_succ i.isLt) j

theorem card_supportedPatterns {d r : ℕ} {μ : Fin d → ℤ} (hrd : r ≤ d)
    (hμ : Dominant μ) (hnonneg : ∀ j, 0 ≤ μ j)
    (hzero : ∀ i : Fin d, r ≤ i.val → μ i = 0) :
    Fintype.card (SupportedPatterns μ r) = Fintype.card (Pattern (restrictRow hrd μ)) :=
  Fintype.card_congr (rankSupportEquiv hrd hμ hnonneg hzero)

/-- A supported weight offset gives a supported GT weight when the top row is supported. -/
def offsetToSupported {d r : ℕ} {μ δ : Fin d → ℤ}
    (hμzero : ∀ i : Fin d, r ≤ i.val → μ i = 0)
    (hδzero : ∀ i : Fin d, r ≤ i.val → δ i = 0)
    (P : OffsetPatterns μ δ) : SupportedPatterns μ r :=
  ⟨P.val, by
    intro i hi
    have hw := congrFun P.property i
    simpa only [Pi.sub_apply, hμzero i hi, hδzero i hi, sub_self] using hw⟩

/-- Restriction preserves the exact ordinary weight offset. -/
def restrictOffsetPattern {d r : ℕ} {μ δ : Fin d → ℤ} (hrd : r ≤ d)
    (hnonneg : ∀ j, 0 ≤ μ j)
    (hμzero : ∀ i : Fin d, r ≤ i.val → μ i = 0)
    (hδzero : ∀ i : Fin d, r ≤ i.val → δ i = 0)
    (P : OffsetPatterns μ δ) : OffsetPatterns (restrictRow hrd μ) (restrictRow hrd δ) :=
  ⟨restrictPattern hrd hnonneg (offsetToSupported hμzero hδzero P), by
    funext i
    exact congrFun P.property (i.castLE hrd)⟩

/-- Padding preserves the exact ordinary weight offset, including its zero trailing entries. -/
def padOffsetPattern {d r : ℕ} {μ δ : Fin d → ℤ} (hrd : r ≤ d) (hμ : Dominant μ)
    (_hμzero : ∀ i : Fin d, r ≤ i.val → μ i = 0)
    (hδzero : ∀ i : Fin d, r ≤ i.val → δ i = 0)
    (P : OffsetPatterns (restrictRow hrd μ) (restrictRow hrd δ)) : OffsetPatterns μ δ :=
  ⟨padPattern hrd hμ P.val, by
    funext i
    by_cases hi : i.val < r
    · let ir : Fin r := ⟨i.val, hi⟩
      have hir : ir.castLE hrd = i := Fin.ext rfl
      rw [← hir, weight_padPattern_low]
      exact congrFun P.property ir
    · have hir : r ≤ i.val := by omega
      rw [weight_padPattern_high hrd hμ P.val i hir]
      simp only [Pi.sub_apply, hδzero i hir, sub_zero]⟩

/-- Full ambient and rank-restricted GT patterns at the same supported offset are equivalent. -/
def rankOffsetEquiv {d r : ℕ} {μ δ : Fin d → ℤ} (hrd : r ≤ d)
    (hμ : Dominant μ) (hnonneg : ∀ j, 0 ≤ μ j)
    (hμzero : ∀ i : Fin d, r ≤ i.val → μ i = 0)
    (hδzero : ∀ i : Fin d, r ≤ i.val → δ i = 0) :
    OffsetPatterns μ δ ≃ OffsetPatterns (restrictRow hrd μ) (restrictRow hrd δ) where
  toFun := restrictOffsetPattern hrd hnonneg hμzero hδzero
  invFun := padOffsetPattern hrd hμ hμzero hδzero
  left_inv P := by
    apply Subtype.ext
    exact congrArg (fun Q : SupportedPatterns μ r => Q.val)
      ((rankSupportEquiv hrd hμ hnonneg hμzero).left_inv
      (offsetToSupported hμzero hδzero P))
  right_inv P := by
    apply Subtype.ext
    exact (rankSupportEquiv hrd hμ hnonneg hμzero).right_inv P.val

/-- The exact rank-support multiplicity identity for actual integer GT counts. -/
theorem multiplicity_rankSupport {d r : ℕ} {μ δ : Fin d → ℤ} (hrd : r ≤ d)
    (hμ : Dominant μ) (hnonneg : ∀ j, 0 ≤ μ j)
    (hμzero : ∀ i : Fin d, r ≤ i.val → μ i = 0)
    (hδzero : ∀ i : Fin d, r ≤ i.val → δ i = 0) :
    multiplicity μ δ = multiplicity (restrictRow hrd μ) (restrictRow hrd δ) :=
  Fintype.card_congr (rankOffsetEquiv hrd hμ hnonneg hμzero hδzero)

/-- Rank support in the cut-coordinate convention used by the Theorem 2 GT bounds. -/
theorem multiplicity_rankSupport_cuts {d r : ℕ} {μ : Fin d → ℤ} (hrd : r ≤ d)
    (hμ : Dominant μ) (hnonneg : ∀ j, 0 ≤ μ j)
    (hμzero : ∀ i : Fin d, r ≤ i.val → μ i = 0)
    (δ : ℕ → ℕ) (hδ : ValidCuts r δ) :
    multiplicity μ (coordinateOffset d δ) =
      multiplicity (restrictRow hrd μ) (coordinateOffset r δ) := by
  have hz : ∀ i : Fin d, r ≤ i.val → coordinateOffset d δ i = 0 := by
    intro i hi
    simp only [coordinateOffset, hδ.2 i.val hi, hδ.2 (i.val + 1) (by omega),
      Nat.cast_zero, sub_self]
  exact multiplicity_rankSupport hrd hμ hnonneg hμzero hz

end FreeEntropy.GelfandTsetlin
