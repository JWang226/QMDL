/-
Copyright (c) 2026 Free Entropy formalization contributors.
See LICENSE and NOTICE in the repository root for license and attribution.
-/

import FreeEntropy.PhysicalOrbitChannels
import FreeEntropy.CanonicalConverse
import FreeEntropy.CanonicalRowBounds

/-! The actual typical physical highest rows satisfy every geometric row
condition of the cloning construction with the manuscript's padded target.
The estimates are uniform over all physical sectors. -/
noncomputable section
open Filter
open scoped BigOperators Topology
namespace FreeEntropy.SchurWeyl
open ExteriorRepresentation TypicalRows CasimirWeights
set_option backward.isDefEq.respectTransparency false
variable {d r n : ℕ}

theorem occupationRow_cast_fin (lam : Occupation.Occupation d n) (j : Fin d) :
    (occupationRow lam j.val : ℝ) = (lam.val j : ℝ) := by
  simp only [occupationRow, dif_pos j.isLt, Int.cast_natCast]

theorem targetCanonicalRow_supported (s : FixedSpectrum d r) (n : ℕ)
    (j : Fin d) (hj : r ≤ j.val) : targetCanonicalRow s n j = 0 := by
  have h : (targetCanonicalRow s n j : ℝ) = 0 := by
    simp only [targetCanonicalRow, targetNaturalRow_cast, FixedSpectrum.targetRow,
      if_neg (by omega : ¬ j.val < r)]
  exact_mod_cast h

theorem typicalCanonical_le_target (s : FixedSpectrum d r) (n : ℕ) (hn : 1 ≤ n)
    (lam : Occupation.Occupation d n) (ht : Typical s n (occupationRow lam)) :
    ∀ j, lam.val j ≤ targetCanonicalRow s n j := by
  intro j
  by_cases hj : j.val < r
  · have h := (row_surplus_bounds s n hn _ ht j.val hj).1
    rw [occupationRow_cast_fin] at h
    have he := targetNaturalRow_cast s n j.val
    change (targetCanonicalRow s n j : ℝ) = _ at he
    rw [← he] at h
    exact_mod_cast (sub_nonneg.mp h)
  · have h := ht.2 j.val (by omega) j.isLt
    simp only [occupationRow, dif_pos j.isLt] at h
    have hz : lam.val j = 0 := by exact_mod_cast h
    simp only [hz, Nat.zero_le]

theorem typicalCanonical_increment_antitone (s : FixedSpectrum d r) (n : ℕ) (hn : 1 ≤ n)
    (lam : Occupation.Occupation d n) (ht : Typical s n (occupationRow lam)) :
    Antitone (fun j : Fin d => (targetCanonicalRow s n j : ℝ) - (lam.val j : ℝ)) := by
  intro i j hij
  rcases eq_or_lt_of_le hij with h | h
  · subst j; exact le_rfl
  · have hh := target_difference_dominant s n hn _ ht i.val j.val h j.isLt
    simpa only [targetCanonicalRow, targetNaturalRow_cast, occupationRow_cast_fin] using hh

theorem typicalCanonical_natural_increment_antitone (s : FixedSpectrum d r)
    (n : ℕ) (hn : 1 ≤ n) (lam : Occupation.Occupation d n)
    (ht : Typical s n (occupationRow lam)) :
    Antitone (fun j : Fin d => targetCanonicalRow s n j - lam.val j) := by
  intro i j hij
  have hh := typicalCanonical_increment_antitone s n hn lam ht hij
  have hle := typicalCanonical_le_target s n hn lam ht
  have he (k : Fin d) : ((targetCanonicalRow s n k - lam.val k : ℕ) : ℝ) =
      (targetCanonicalRow s n k : ℝ) - (lam.val k : ℝ) := Nat.cast_sub (hle k)
  dsimp only at hh
  rw [← he i, ← he j] at hh
  exact_mod_cast hh

theorem typicalCanonical_supported (s : FixedSpectrum d r) (n : ℕ)
    (lam : Occupation.Occupation d n) (ht : Typical s n (occupationRow lam))
    (j : Fin d) (hj : r ≤ j.val) : lam.val j = 0 := by
  have h := ht.2 j.val hj j.isLt
  simp only [occupationRow, dif_pos j.isLt] at h
  exact_mod_cast h

theorem typicalCanonical_increment_zero_tail (s : FixedSpectrum d r) (n : ℕ)
    (lam : Occupation.Occupation d n) (ht : Typical s n (occupationRow lam))
    (j : Fin d) (hj : r ≤ j.val) :
    (targetCanonicalRow s n j : ℝ) - (lam.val j : ℝ) = 0 := by
  rw [targetCanonicalRow_supported s n j hj, typicalCanonical_supported s n lam ht j hj]
  simp only [Nat.cast_zero, sub_zero]

/-- Padding supplies at least one unit of surplus in every supported row. -/
theorem typical_row_surplus_one (s : FixedSpectrum d r) (n : ℕ) (hn : 1 ≤ n)
    (mu : ℕ → ℤ) (ht : Typical s n mu) (j : ℕ) (hj : j < r) :
    1 ≤ s.targetRow n j - (mu j : ℝ) := by
  have hw := width_nonneg n hn
  have htyp := (abs_le.mp (ht.1 j hj)).2
  have hk : (1 : ℝ) ≤ (r - j : ℕ) := by exact_mod_cast (show 1 ≤ r - j by omega)
  have hceil := Int.le_ceil ((n : ℝ) * s.eigenvalue j +
    (r - j : ℕ) * (2 * typicalWidth n + 1))
  simp only [FixedSpectrum.targetRow, hj, ↓reduceIte, paddedRow]
  nlinarith

theorem typicalCanonical_distance_ge_one (s : FixedSpectrum d r) (n : ℕ) (hn : 1 ≤ n)
    (lam : Occupation.Occupation d n) (ht : Typical s n (occupationRow lam)) :
    1 ≤ Weyl.rowL1 d (fun j => s.targetRow n j - (occupationRow lam j : ℝ)) := by
  have hd : 0 < d := lt_of_lt_of_le s.rank_pos s.rank_le
  have h := typical_row_surplus_one s n hn _ ht 0 s.rank_pos
  unfold Weyl.rowL1
  have hsum := Finset.single_le_sum (f := fun j =>
    |s.targetRow n j - (occupationRow lam j : ℝ)|)
    (fun j (_ : j ∈ Finset.range d) => abs_nonneg _) (Finset.mem_range.mpr hd)
  exact h.trans ((le_abs_self _).trans hsum)

/-- Both actual rows have the same eventual linear supported gap. -/
theorem typicalCanonical_eventually_gaps (s : FixedSpectrum d r) (hd : 2 ≤ d) :
    ∀ᶠ n in atTop, ∀ lam : Occupation.Occupation d n,
      Typical s n (occupationRow lam) → ∀ j : Fin (d - 1), j.val < r →
      (n : ℝ) * minimumGap s hd / 2 ≤ (lam.val (left j) : ℝ) - lam.val (right j) ∧
      (n : ℝ) * minimumGap s hd / 2 ≤
        (targetCanonicalRow s n (left j) : ℝ) - targetCanonicalRow s n (right j) := by
  filter_upwards [eventually_uniform_gap s hd, eventually_ge_atTop 1] with n hg hn
  intro lam ht j hj
  have hjd : j.val + 1 < d := by omega
  have h := hg _ ht j.val hj hjd
  have hcast : (occupationRow lam j.val : ℝ) = (lam.val (left j) : ℝ) :=
    occupationRow_cast_fin lam (left j)
  have hsucc : (occupationRow lam (j.val + 1) : ℝ) = (lam.val (right j) : ℝ) :=
    occupationRow_cast_fin lam (right j)
  rw [hcast, hsucc] at h
  refine ⟨h, ?_⟩
  have hi := typicalCanonical_increment_antitone s n hn lam ht (show left j ≤ right j by simp only [left, right, Fin.le_def]; omega)
  linarith

/-- The finite row norm agrees with the manuscript's ambient row norm. -/
theorem typicalCanonical_l1_eq (s : FixedSpectrum d r) (n : ℕ)
    (lam : Occupation.Occupation d n) :
    l1 (fun j => (targetCanonicalRow s n j : ℝ) - (lam.val j : ℝ)) =
      Weyl.rowL1 d (fun j => s.targetRow n j - (occupationRow lam j : ℝ)) := by
  unfold l1 Weyl.rowL1
  rw [← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro j _
  dsimp only
  rw [occupationRow_cast_fin]
  simp only [targetCanonicalRow, targetNaturalRow_cast]

/-- The exact typical-row finite cloning envelope has the claimed rate. -/
theorem typicalCanonical_envelope_le (s : FixedSpectrum d r) (hd : 2 ≤ d)
    (K : ℝ) (hK : 0 ≤ K) (n : ℕ) (hn : 2 ≤ n)
    (lam : Occupation.Occupation d n) (ht : Typical s n (occupationRow lam)) :
    K * l1 (fun j => (targetCanonicalRow s n j : ℝ) - (lam.val j : ℝ)) /
      ((n : ℝ) * minimumGap s hd / 2 + 1) ≤
      (2 * K * ((r : ℝ) * (3 * r + 2)) / minimumGap s hd) * Weyl.errorScale n := by
  rw [typicalCanonical_l1_eq]
  exact cloning_envelope_le s hd K hK n hn _ ht

theorem typicalCanonical_differenceNorm_pos (s : FixedSpectrum d r) (n : ℕ) (hn : 1 ≤ n)
    (lam : Occupation.Occupation d n) (ht : Typical s n (occupationRow lam)) :
    1 ≤ differenceNorm lam.val (targetCanonicalRow s n) := by
  have h := typicalCanonical_distance_ge_one s n hn lam ht
  rw [← typicalCanonical_l1_eq, ← differenceNorm_cast] at h
  exact_mod_cast h

/-- The computed natural minimum gap dominates the uniform real gap. -/
theorem typicalCanonical_eventually_minimumGap (s : FixedSpectrum d r) (hd : 2 ≤ d) :
    ∀ᶠ n in atTop, ∀ lam : Occupation.Occupation d n, Antitone lam.val →
      Typical s n (occupationRow lam) →
      (n : ℝ) * minimumGap s hd / 2 ≤
        (minimumRowGap lam.val r hd s.rank_pos : ℝ) := by
  filter_upwards [typicalCanonical_eventually_gaps s hd] with n hn
  intro lam hanti ht
  exact le_minimumRowGap lam.val hanti r hd s.rank_pos _ (fun j hj => (hn lam ht j hj).1)

end FreeEntropy.SchurWeyl
