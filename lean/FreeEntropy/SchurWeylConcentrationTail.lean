/-
Copyright (c) 2026 Free Entropy formalization contributors.
See LICENSE and NOTICE in the repository root for license and attribution.
-/

import FreeEntropy.SchurWeylConcentrationProbability

/-! Concentration of the actual physical tensor source. The estimate includes
zero eigenvalues and uses the manuscript's actual typical window. -/
noncomputable section
open Matrix Filter
open scoped BigOperators Topology
namespace FreeEntropy.SchurWeyl
open Occupation WordTypes FiniteConcentration
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
attribute [local instance] Classical.propDecidable
variable {d n : ℕ}

theorem occupation_card_le (d n : ℕ) : Fintype.card (Occupation d n) ≤ (n + 1) ^ d := by
  let code : Occupation d n → Fin d → Fin (n + 1) := fun lam j =>
    ⟨lam.val j, by
      have h := Finset.single_le_sum (fun i (_ : i ∈ Finset.univ) => Nat.zero_le (lam.val i))
        (Finset.mem_univ j)
      rw [lam.property] at h
      omega⟩
  apply diagram_card_le d n code
  intro a b h
  apply Subtype.ext
  funext j
  exact congrArg Fin.val (congrFun h j)

/-- A general L1-separated collection of actual highest occupations has
exponentially small physical mass. Unsupported rows have exactly zero mass. -/
theorem physical_grouped_tail_le (n : ℕ) (hn : 0 < n) (x : Fin d → ℝ)
    (hx : ∀ j, 0 ≤ x j) (hanti : Antitone x) (hx1 : ∑ j, x j = 1)
    (bad : Finset (Occupation d n)) (ε : ℝ) (hε : 0 ≤ ε)
    (hbad : ∀ lam ∈ bad, (∀ j, lam.val j ≠ 0 → 0 < x j) →
      ε ≤ l1 (empirical lam.val n) x) :
    (∑ lam ∈ bad, highestSectorMass lam x) ≤
      ((n : ℝ) + 1) ^ (concentrationExponent d + d) *
        Real.exp (-(n : ℝ) * ε ^ 2 / 4) := by
  have hterm (lam : Occupation d n) (hlam : lam ∈ bad) : highestSectorMass lam x ≤
      ((n : ℝ) + 1) ^ concentrationExponent d * Real.exp (-(n : ℝ) * ε ^ 2 / 4) := by
    by_cases hs : ∀ j, lam.val j ≠ 0 → 0 < x j
    · have hk := l1_sq_div_four_le_kl_of_support (empirical lam.val n) x
        (fun i => div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) hx
        (fun i hi => by
          have hl : lam.val i = 0 := by
            by_contra hne
            have h := hs i hne
            linarith
          simp [empirical, hl]) (empirical_sum lam.val hn lam.property) hx1
      have hl : 0 ≤ l1 (empirical lam.val n) x := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
      have hsquare := (sq_le_sq₀ hε hl).mpr (hbad lam hlam hs)
      have he : -(n : ℝ) * kl (empirical lam.val n) x ≤ -(n : ℝ) * ε ^ 2 / 4 := by
        have hm := mul_le_mul_of_nonneg_left
          (show ε ^ 2 / 4 ≤ kl (empirical lam.val n) x by linarith)
          (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
        nlinarith
      exact (highestSectorMass_le_exp_neg_kl lam hn x hx hanti hs).trans
        (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr he) (by positivity))
    · push_neg at hs
      obtain ⟨j, hj, hxj⟩ := hs
      exact (highestSectorMass_le_zero_of_unsupported lam x hx hanti j
        (le_antisymm hxj (hx j)) hj).trans (by positivity)
  have hcard : (bad.card : ℝ) ≤ ((n : ℝ) + 1) ^ d := by
    have hc := bad.card_le_univ.trans (occupation_card_le d n)
    exact_mod_cast hc
  calc
    (∑ lam ∈ bad, highestSectorMass lam x) ≤ ∑ _lam ∈ bad,
        ((n : ℝ) + 1) ^ concentrationExponent d * Real.exp (-(n : ℝ) * ε ^ 2 / 4) :=
      Finset.sum_le_sum hterm
    _ = (bad.card : ℝ) * (((n : ℝ) + 1) ^ concentrationExponent d *
        Real.exp (-(n : ℝ) * ε ^ 2 / 4)) := by simp
    _ ≤ ((n : ℝ) + 1) ^ d * (((n : ℝ) + 1) ^ concentrationExponent d *
        Real.exp (-(n : ℝ) * ε ^ 2 / 4)) :=
      mul_le_mul_of_nonneg_right hcard (by positivity)
    _ = _ := by rw [pow_add]; ring

/-- The integer row used by the manuscript's typicality definition. -/
def occupationRow (lam : Occupation d n) (j : ℕ) : ℤ :=
  if hj : j < d then (lam.val ⟨j, hj⟩ : ℤ) else 0

variable {r : ℕ}

def physicalSpectrum (s : FixedSpectrum d r) : Fin d → ℝ := fun j => s.eigenvalue j

theorem physicalSpectrum_nonneg (s : FixedSpectrum d r) (j : Fin d) :
    0 ≤ physicalSpectrum s j := by
  by_cases hj : j.val < r
  · exact (s.positive _ hj).le
  · simp only [physicalSpectrum, s.zero_padded _ (by omega) j.isLt, le_refl]

theorem physicalSpectrum_antitone (s : FixedSpectrum d r) : Antitone (physicalSpectrum s) := by
  intro i j hij
  by_cases hj : j.val < r
  · rcases lt_or_eq_of_le hij with hij' | rfl
    · exact (s.decreasing _ _ hij' hj).le
    · rfl
  · have hz := s.zero_padded _ (show r ≤ j.val by omega) j.isLt
    change s.eigenvalue j ≤ s.eigenvalue i
    rw [hz]
    exact physicalSpectrum_nonneg s i

theorem physicalSpectrum_normalized (s : FixedSpectrum d r) :
    ∑ j, physicalSpectrum s j = 1 := by
  change (∑ j : Fin d, s.eigenvalue j) = 1
  rw [Fin.sum_univ_eq_sum_range]
  calc
    ∑ j ∈ Finset.range d, s.eigenvalue j = ∑ j ∈ Finset.range r, s.eigenvalue j := by
      symm
      apply Finset.sum_subset (Finset.range_mono s.rank_le)
      intro j hj hjr
      exact s.zero_padded j (by simpa using hjr) (by simpa using hj)
    _ = 1 := s.normalized

/-- Failure of actual typicality implies the L1 separation after support is
established; the factor two follows from normalization, including zero coordinates. -/
theorem occupation_notTypical_l1 (s : FixedSpectrum d r) (n : ℕ) (hn : 2 ≤ n)
    (lam : Occupation d n)
    (hsupp : ∀ j, lam.val j ≠ 0 → 0 < physicalSpectrum s j)
    (hnot : ¬ TypicalRows.Typical s n (occupationRow lam)) :
    Real.logb 2 n / Real.sqrt n ≤ l1 (empirical lam.val n) (physicalSpectrum s) := by
  have hzero : ∀ j, r ≤ j → j < d → occupationRow lam j = 0 := by
    intro j hj hjd
    have he : lam.val ⟨j, hjd⟩ = 0 := by
      by_contra hne
      have h := hsupp ⟨j, hjd⟩ hne
      change 0 < s.eigenvalue j at h
      rw [s.zero_padded j hj hjd] at h
      exact (lt_irrefl _) h
    simp [occupationRow, hjd, he]
  have hf : ¬ ∀ j, j < r → |(occupationRow lam j : ℝ) -
      (n : ℝ) * s.eigenvalue j| ≤ typicalWidth n := fun h => hnot ⟨h, hzero⟩
  push_neg at hf
  obtain ⟨j, hj, hdev⟩ := hf
  have hjd : j < d := lt_of_lt_of_le hj s.rank_le
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hs : 0 < Real.sqrt n := Real.sqrt_pos.mpr hn0
  have hl : 0 ≤ Real.logb 2 n := Real.logb_nonneg (by norm_num)
    (by exact_mod_cast (show 1 ≤ n by omega))
  have hcoord := coordinate_abs_le_half_l1 (empirical lam.val n) (physicalSpectrum s)
    ((empirical_sum lam.val (by omega) lam.property).trans (physicalSpectrum_normalized s).symm)
    ⟨j, hjd⟩
  simp only [occupationRow, dif_pos hjd, Int.cast_natCast] at hdev
  change |(lam.val ⟨j, hjd⟩ : ℝ) / n - s.eigenvalue j| ≤ _ at hcoord
  have hid : |(lam.val ⟨j, hjd⟩ : ℝ) - (n : ℝ) * s.eigenvalue j| =
      (n : ℝ) * |(lam.val ⟨j, hjd⟩ : ℝ) / n - s.eigenvalue j| := by
    have he : (lam.val ⟨j, hjd⟩ : ℝ) - (n : ℝ) * s.eigenvalue j =
        (n : ℝ) * ((lam.val ⟨j, hjd⟩ : ℝ) / n - s.eigenvalue j) := by field_simp
    rw [he, abs_mul, abs_of_pos hn0]
  rw [hid] at hdev
  have hm := mul_le_mul_of_nonneg_left hcoord hn0.le
  have hs2 := Real.sq_sqrt (show 0 ≤ (n : ℝ) / 2 by positivity)
  have hs1 := Real.sq_sqrt hn0.le
  have hscomp : Real.sqrt n ≤ 2 * Real.sqrt ((n : ℝ) / 2) := by
    nlinarith [Real.sqrt_nonneg ((n : ℝ) / 2)]
  have hw : Real.sqrt n * Real.logb 2 n ≤ 2 * typicalWidth n := by
    have hh := mul_le_mul_of_nonneg_right hscomp hl
    simpa only [typicalWidth, mul_assoc] using hh
  have hnL : Real.sqrt n * Real.logb 2 n ≤
      (n : ℝ) * l1 (empirical lam.val n) (physicalSpectrum s) := by linarith
  apply (div_le_iff₀ hs).mpr
  nlinarith [mul_le_mul_of_nonneg_left hnL (inv_nonneg.mpr hs.le), inv_mul_cancel₀ hs.ne']

/-- The actual physical grouped probability outside the actual supported
typical window has the squared-log concentration bound. -/
theorem physical_atypical_grouped_tail_le (s : FixedSpectrum d r) (n : ℕ) (hn : 2 ≤ n) :
    (∑ lam ∈ Finset.univ.filter (fun lam : Occupation d n =>
      ¬ TypicalRows.Typical s n (occupationRow lam)), highestSectorMass lam (physicalSpectrum s)) ≤
        Concentration.tailBound (concentrationExponent d + d) n := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have he : 0 ≤ Real.logb 2 n / Real.sqrt n := div_nonneg
    (Real.logb_nonneg (by norm_num) (by exact_mod_cast (show 1 ≤ n by omega)))
    (Real.sqrt_nonneg _)
  have h := physical_grouped_tail_le n (by omega) (physicalSpectrum s)
    (physicalSpectrum_nonneg s) (physicalSpectrum_antitone s) (physicalSpectrum_normalized s)
    (Finset.univ.filter (fun lam => ¬ TypicalRows.Typical s n (occupationRow lam))) _ he
    (fun lam hlam hsupp => occupation_notTypical_l1 s n hn lam hsupp (Finset.mem_filter.mp hlam).2)
  have hid : -(n : ℝ) * (Real.logb 2 n / Real.sqrt n) ^ 2 / 4 = -(Real.logb 2 n) ^ 2 / 4 := by
    rw [div_pow, Real.sq_sqrt hn0.le]
    field_simp
  simpa only [hid, Concentration.tailBound] using h

end FreeEntropy.SchurWeyl
