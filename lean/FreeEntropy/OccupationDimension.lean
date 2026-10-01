/-
Copyright (c) 2026 Free Entropy formalization contributors.
See LICENSE and NOTICE in the repository root for license and attribution.
-/

import FreeEntropy.Occupation
import FreeEntropy.OccupationCounting

/-!
# Exact dimension and rate of the occupation memory

The memory indices are the occupations used in the explicit symmetric
tensor isometry. Their proved stars-and-bars cardinality has the exact
rank-one qmdl expansion, including the factorial constant.
-/

noncomputable section
open Filter
open scoped BigOperators Topology

namespace FreeEntropy.Occupation

theorem card_occupation (d n : ℕ) :
    Fintype.card (Occupation d n) = (d + n - 1).choose n := by
  rw [← Nat.card_eq_fintype_card]
  exact OccupationCounting.card_compositions d n

theorem card_occupation_symm (d n : ℕ) (hd : 0 < d) :
    Fintype.card (Occupation d n) = (n + (d - 1)).choose (d - 1) := by
  rw [← Nat.card_eq_fintype_card]
  exact OccupationCounting.card_compositions_symm d n hd

theorem occupationDimension_pos (d n : ℕ) (hd : 0 < d) :
    0 < Fintype.card (Occupation d n) := by
  rw [card_occupation_symm d n hd]
  exact Nat.choose_pos (by omega)

/-- The occupation memory has the exact leading term and factorial constant. -/
theorem occupation_log_asymptotic (d : ℕ) (hd : 0 < d) :
    Tendsto (fun n : ℕ => Real.logb 2 (Fintype.card (Occupation d n)) -
      (((d - 1 : ℕ) : ℝ) * Real.logb 2 n - Real.logb 2 ((d - 1).factorial : ℝ)))
      atTop (𝓝 0) := by
  simpa only [card_occupation_symm d _ hd] using
    OccupationCounting.choose_log_asymptotic (d - 1)

/-- For a normalized rank-one spectrum this is exactly the manuscript's
`L_{d,1}`, with no representation dimension premise. -/
theorem occupation_qmdl_asymptotic {d : ℕ} (s : FixedSpectrum d 1) :
    Tendsto (fun n : ℕ => Real.logb 2 (Fintype.card (Occupation d n)) -
      Weyl.qmdl d 1 s.eigenvalue n) atTop (𝓝 0) := by
  have hd : 0 < d := lt_of_lt_of_le s.rank_pos s.rank_le
  have hx : s.eigenvalue 0 = 1 := by simpa using s.normalized
  simpa only [OccupationCounting.qmdl_rank_one d _ hd s.eigenvalue hx] using
    occupation_log_asymptotic d hd

end FreeEntropy.Occupation
