/-
Copyright (c) 2026 Free Entropy formalization contributors.
See LICENSE and NOTICE in the repository root for license and attribution.
-/

import FreeEntropy.CanonicalDimensionRatio

/-! Exact natural row norms and minimum gaps for the finite cloning theorem.
These are computed from the two highest rows, not supplied as witnesses. -/
noncomputable section
open scoped BigOperators
namespace FreeEntropy.ExteriorRepresentation
open CasimirWeights
set_option backward.isDefEq.respectTransparency false
variable {d : ℕ}

def differenceNorm (mu nu : Fin d → ℕ) : ℕ :=
  ∑ i, Int.natAbs ((nu i : ℤ) - (mu i : ℤ))

theorem differenceNorm_cast (mu nu : Fin d → ℕ) :
    (differenceNorm mu nu : ℝ) = l1 (fun i => (nu i : ℝ) - (mu i : ℝ)) := by
  unfold differenceNorm l1
  rw [Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [← Int.cast_natCast, Int.natCast_natAbs, Int.cast_abs, Int.cast_sub,
    Int.cast_natCast, Int.cast_natCast]

theorem differenceNorm_zero_iff (mu nu : Fin d → ℕ) : differenceNorm mu nu = 0 ↔ nu = mu := by
  constructor
  · intro h
    funext i
    have hi := Finset.single_le_sum (s := Finset.univ)
      (f := fun j => Int.natAbs ((nu j : ℤ) - (mu j : ℤ)))
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
    change Int.natAbs ((nu i : ℤ) - (mu i : ℤ)) ≤ differenceNorm mu nu at hi
    rw [h] at hi
    have hz : (nu i : ℤ) - (mu i : ℤ) = 0 := Int.natAbs_eq_zero.mp (Nat.eq_zero_of_le_zero hi)
    exact_mod_cast sub_eq_zero.mp hz
  · rintro rfl
    simp [differenceNorm]

theorem differenceNorm_pos (mu nu : Fin d → ℕ) (h : nu ≠ mu) : 1 ≤ differenceNorm mu nu :=
  Nat.one_le_iff_ne_zero.mpr (fun hz => h ((differenceNorm_zero_iff mu nu).mp hz))

def supportedGapIndices (d rank : ℕ) : Finset (Fin (d - 1)) :=
  Finset.univ.filter (fun j => j.val < rank)

theorem supportedGapIndices_nonempty (rank : ℕ) (hd : 2 ≤ d) (hr : 0 < rank) :
    (supportedGapIndices d rank).Nonempty := by
  exact ⟨⟨0, by omega⟩, by simp [supportedGapIndices, hr]⟩

def minimumRowGap (mu : Fin d → ℕ) (rank : ℕ) (hd : 2 ≤ d) (hr : 0 < rank) : ℕ :=
  (supportedGapIndices d rank).inf' (supportedGapIndices_nonempty rank hd hr)
    (fun j => mu (left j) - mu (right j))

theorem minimumRowGap_le (mu : Fin d → ℕ) (rank : ℕ) (hd : 2 ≤ d) (hr : 0 < rank)
    (j : Fin (d - 1)) (hj : j.val < rank) :
    minimumRowGap mu rank hd hr ≤ mu (left j) - mu (right j) := by
  exact Finset.inf'_le (s := supportedGapIndices d rank)
    (fun j => mu (left j) - mu (right j))
    (Finset.mem_filter.mpr ⟨Finset.mem_univ j, hj⟩)

theorem minimumRowGap_cast_le (mu : Fin d → ℕ) (hmu : Antitone mu)
    (rank : ℕ) (hd : 2 ≤ d) (hr : 0 < rank) (j : Fin (d - 1)) (hj : j.val < rank) :
    (minimumRowGap mu rank hd hr : ℝ) ≤ (mu (left j) : ℝ) - (mu (right j) : ℝ) := by
  have hmono : mu (right j) ≤ mu (left j) := hmu (by change j.val ≤ j.val + 1; omega)
  have h := minimumRowGap_le mu rank hd hr j hj
  exact_mod_cast h

/-- Every real uniform adjacent-gap bound also bounds the actual integral minimum. -/
theorem le_minimumRowGap (mu : Fin d → ℕ) (hmu : Antitone mu)
    (rank : ℕ) (hd : 2 ≤ d) (hr : 0 < rank) (b : ℝ)
    (hb : ∀ j : Fin (d - 1), j.val < rank → b ≤ (mu (left j) : ℝ) - (mu (right j) : ℝ)) :
    b ≤ (minimumRowGap mu rank hd hr : ℝ) := by
  obtain ⟨j, hj, he⟩ := Finset.exists_mem_eq_inf'
    (supportedGapIndices_nonempty rank hd hr) (fun j => mu (left j) - mu (right j))
  change b ≤ ((supportedGapIndices d rank).inf' _ _ : ℕ)
  rw [he, Nat.cast_sub (hmu (by change j.val ≤ j.val + 1; omega))]
  exact hb j (Finset.mem_filter.mp hj).2

end FreeEntropy.ExteriorRepresentation
