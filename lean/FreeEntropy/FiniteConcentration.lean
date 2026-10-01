/-
Copyright (c) 2026 Free Entropy formalization contributors.
See LICENSE and NOTICE in the repository root for license and attribution.
-/

import FreeEntropy.Concentration
import FreeEntropy.TypicalRows
import Mathlib.InformationTheory.KullbackLeibler.KLFun
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.Card

/-!
# Finite classical concentration from an explicit Schur probability bound

The analytic argument proves `KL(p || q) ≥ TV(p,q)^2` using Hellinger
distance and finite Cauchy–Schwarz. This is weaker by a factor two than
optimal Pinsker, and is explicitly named accordingly. It is sufficient for
the manuscript's conservative squared-log tail bound. The pointwise
Schur–Weyl probability estimate remains an explicit hypothesis.
-/

noncomputable section
open scoped BigOperators
open Real InformationTheory
namespace FreeEntropy.FiniteConcentration
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000

variable {ι : Type*} [Fintype ι]

/-- Natural-log classical relative entropy; the reference distribution will
be strictly positive. The `p_i = 0` terms use the usual zero convention. -/
def kl (p q : ι → ℝ) : ℝ := ∑ i, p i * Real.log (p i / q i)

def l1 (p q : ι → ℝ) : ℝ := ∑ i, |p i - q i|

def tv (p q : ι → ℝ) : ℝ := l1 p q / 2

def hellingerSq (p q : ι → ℝ) : ℝ := ∑ i, (Real.sqrt (p i) - Real.sqrt (q i)) ^ 2

/-- Scalar KL/Hellinger inequality, valid at zero as well. -/
theorem klFun_ge_sqrt (t : ℝ) (ht : 0 ≤ t) : (Real.sqrt t - 1) ^ 2 ≤ klFun t := by
  have hn := mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) (Real.sqrt_nonneg t))
    (klFun_nonneg (Real.sqrt_nonneg t))
  have hid : klFun t - (Real.sqrt t - 1) ^ 2 = 2 * Real.sqrt t * klFun (Real.sqrt t) := by
    unfold klFun
    rw [Real.log_sqrt ht]
    ring_nf
    rw [Real.sq_sqrt ht]
    ring
  linarith

theorem weighted_klFun_ge_sqrt {p q : ℝ} (hp : 0 ≤ p) (hq : 0 < q) :
    (Real.sqrt p - Real.sqrt q) ^ 2 ≤ q * klFun (p / q) := by
  have h := mul_le_mul_of_nonneg_left (klFun_ge_sqrt (p / q) (div_nonneg hp hq.le)) hq.le
  have hid : q * (Real.sqrt (p / q) - 1) ^ 2 = (Real.sqrt p - Real.sqrt q) ^ 2 := by
    rw [Real.sqrt_div hp]
    have hs : Real.sqrt q ≠ 0 := (Real.sqrt_pos.mpr hq).ne'
    field_simp
    nlinarith [Real.sq_sqrt hq.le]
  rwa [hid] at h

/-- Affine terms in the normalized KL function cancel for probabilities. -/
theorem kl_eq_weighted_klFun (p q : ι → ℝ) (hq : ∀ i, 0 < q i)
    (hp1 : ∑ i, p i = 1) (hq1 : ∑ i, q i = 1) :
    kl p q = ∑ i, q i * klFun (p i / q i) := by
  have heach (i : ι) : q i * klFun (p i / q i) =
      p i * Real.log (p i / q i) + q i - p i := by
    unfold klFun
    field_simp [(hq i).ne']
  simp_rw [heach]
  rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, hp1, hq1]
  simp [kl]

theorem hellingerSq_le_kl (p q : ι → ℝ) (hp : ∀ i, 0 ≤ p i) (hq : ∀ i, 0 < q i)
    (hp1 : ∑ i, p i = 1) (hq1 : ∑ i, q i = 1) : hellingerSq p q ≤ kl p q := by
  rw [kl_eq_weighted_klFun p q hq hp1 hq1]
  exact Finset.sum_le_sum (fun i _ => weighted_klFun_ge_sqrt (hp i) (hq i))

theorem l1_sq_le_four_hellingerSq (p q : ι → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hq : ∀ i, 0 ≤ q i)
    (hp1 : ∑ i, p i = 1) (hq1 : ∑ i, q i = 1) :
    (l1 p q) ^ 2 ≤ 4 * hellingerSq p q := by
  have heach (i : ι) : |p i - q i| =
      |Real.sqrt (p i) - Real.sqrt (q i)| * (Real.sqrt (p i) + Real.sqrt (q i)) := by
    have he : p i - q i = (Real.sqrt (p i) - Real.sqrt (q i)) *
        (Real.sqrt (p i) + Real.sqrt (q i)) := by
      nlinarith [Real.sq_sqrt (hp i), Real.sq_sqrt (hq i)]
    rw [he, abs_mul, abs_of_nonneg (add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))]
  have hb : (∑ i, (Real.sqrt (p i) + Real.sqrt (q i)) ^ 2) ≤ 4 := by
    calc
      _ ≤ ∑ i, 2 * (p i + q i) := by
        apply Finset.sum_le_sum
        intro i _
        nlinarith [Real.sq_sqrt (hp i), Real.sq_sqrt (hq i),
          sq_nonneg (Real.sqrt (p i) - Real.sqrt (q i))]
      _ = 4 := by rw [← Finset.mul_sum, Finset.sum_add_distrib, hp1, hq1]; norm_num
  have hc := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
    (fun i => |Real.sqrt (p i) - Real.sqrt (q i)|)
    (fun i => Real.sqrt (p i) + Real.sqrt (q i))
  simp only [← heach, sq_abs] at hc
  have hn : 0 ≤ hellingerSq p q := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  exact hc.trans (by simpa only [hellingerSq, mul_comm] using mul_le_mul_of_nonneg_left hb hn)

/-- A nonoptimal Pinsker inequality, adequate for the squared-log tail
scale: natural-log KL is at least TV squared (optimal constant is two). -/
theorem weak_pinsker (p q : ι → ℝ) (hp : ∀ i, 0 ≤ p i) (hq : ∀ i, 0 < q i)
    (hp1 : ∑ i, p i = 1) (hq1 : ∑ i, q i = 1) : (tv p q) ^ 2 ≤ kl p q := by
  have hl := l1_sq_le_four_hellingerSq p q hp (fun i => (hq i).le) hp1 hq1
  have hk := hellingerSq_le_kl p q hp hq hp1 hq1
  unfold tv
  nlinarith

/-- Direct L1 form of the proved nonoptimal Pinsker bound. -/
theorem l1_sq_div_four_le_kl (p q : ι → ℝ) (hp : ∀ i, 0 ≤ p i) (hq : ∀ i, 0 < q i)
    (hp1 : ∑ i, p i = 1) (hq1 : ∑ i, q i = 1) : (l1 p q) ^ 2 / 4 ≤ kl p q := by
  have h := weak_pinsker p q hp hq hp1 hq1
  unfold tv at h
  nlinarith

/-- Equal total mass doubles every individual coordinate discrepancy
inside the L1 distance. This is the step needed for the actual typical window. -/
theorem coordinate_abs_le_half_l1 [DecidableEq ι] (p q : ι → ℝ)
    (hpq : ∑ j, p j = ∑ j, q j) (i : ι) : |p i - q i| ≤ l1 p q / 2 := by
  have hz : (∑ j, (p j - q j)) = 0 := by rw [Finset.sum_sub_distrib, hpq, sub_self]
  have he := Finset.sum_erase_add Finset.univ (fun j => p j - q j) (Finset.mem_univ i)
  rw [hz] at he
  have he' : (∑ j ∈ Finset.univ.erase i, (p j - q j)) = -(p i - q i) := by linarith
  have ha := Finset.abs_sum_le_sum_abs (fun j => p j - q j) (Finset.univ.erase i)
  rw [he', abs_neg] at ha
  have hsum := Finset.sum_erase_add Finset.univ (fun j => |p j - q j|) (Finset.mem_univ i)
  unfold l1
  linarith

/-- Empirical spectrum of an integral row on its positive-rank coordinates. -/
def rowFrequency (r n : ℕ) (row : ℕ → ℤ) (i : Fin r) : ℝ := (row i : ℝ) / n

theorem rowFrequency_normalized (r n : ℕ) (hn : 0 < n) (row : ℕ → ℤ)
    (hsize : ∑ i : Fin r, row i = (n : ℤ)) : ∑ i, rowFrequency r n row i = 1 := by
  have hs : (∑ i : Fin r, (row i : ℝ)) = (n : ℝ) := by exact_mod_cast hsize
  simp only [rowFrequency, ← Finset.sum_div, hs]
  exact div_self (by exact_mod_cast hn.ne')

/-- Failure of the manuscript's actual supported typical window gives the
L1 separation used by the concentration theorem. Equal total mass provides
the factor two, so the narrower coordinate window is sufficient. -/
theorem notTypical_l1_lower {d r : ℕ} (s : FixedSpectrum d r) (n : ℕ) (hn : 2 ≤ n)
    (row : ℕ → ℤ) (hzero : ∀ i, r ≤ i → i < d → row i = 0)
    (hsize : ∑ i : Fin r, row i = (n : ℤ)) (hnot : ¬ TypicalRows.Typical s n row) :
    Real.logb 2 n / Real.sqrt n ≤
      l1 (rowFrequency r n row) (fun i : Fin r => s.eigenvalue i) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hs : 0 < Real.sqrt n := Real.sqrt_pos.mpr hn0
  have hl : 0 ≤ Real.logb 2 n := Real.logb_nonneg (by norm_num)
    (by exact_mod_cast (show 1 ≤ n by omega))
  have hf : ¬ ∀ i, i < r → |(row i : ℝ) - (n : ℝ) * s.eigenvalue i| ≤ typicalWidth n :=
    fun h => hnot ⟨h, hzero⟩
  push_neg at hf
  obtain ⟨i, hi, hdev⟩ := hf
  have href : (∑ i : Fin r, s.eigenvalue i) = 1 := by
    simpa only [Fin.sum_univ_eq_sum_range] using s.normalized
  have hcoord := coordinate_abs_le_half_l1 (rowFrequency r n row)
    (fun i : Fin r => s.eigenvalue i)
    ((rowFrequency_normalized r n (by omega) row hsize).trans href.symm) ⟨i, hi⟩
  have hid : |(row i : ℝ) - (n : ℝ) * s.eigenvalue i| =
      (n : ℝ) * |(row i : ℝ) / n - s.eigenvalue i| := by
    have he : (row i : ℝ) - (n : ℝ) * s.eigenvalue i =
        (n : ℝ) * ((row i : ℝ) / n - s.eigenvalue i) := by field_simp
    rw [he, abs_mul, abs_of_pos hn0]
  rw [hid] at hdev
  change |(row i : ℝ) / n - s.eigenvalue i| ≤ _ at hcoord
  have hm := mul_le_mul_of_nonneg_left hcoord hn0.le
  have hs2 := Real.sq_sqrt (show 0 ≤ (n : ℝ) / 2 by positivity)
  have hs1 := Real.sq_sqrt hn0.le
  have hscomp : Real.sqrt n ≤ 2 * Real.sqrt ((n : ℝ) / 2) := by
    nlinarith [Real.sqrt_nonneg ((n : ℝ) / 2)]
  have hw : Real.sqrt n * Real.logb 2 n ≤ 2 * typicalWidth n := by
    have hh := mul_le_mul_of_nonneg_right hscomp hl
    simpa only [typicalWidth, mul_assoc] using hh
  have hnL : Real.sqrt n * Real.logb 2 n ≤
      (n : ℝ) * l1 (rowFrequency r n row) (fun i : Fin r => s.eigenvalue i) := by linarith
  apply (div_le_iff₀ hs).mpr
  nlinarith [mul_le_mul_of_nonneg_left hnL (inv_nonneg.mpr hs.le), inv_mul_cancel₀ hs.ne']

/-- Bounded diagram rows give the polynomial diagram count by an actual
injection into all functions `Fin r → Fin (n+1)`. -/
theorem diagram_card_le {Λ : Type*} [Fintype Λ] (r n : ℕ)
    (rows : Λ → Fin r → Fin (n + 1)) (hinj : Function.Injective rows) :
    Fintype.card Λ ≤ (n + 1) ^ r := by
  simpa only [Fintype.card_fun, Fintype.card_fin] using Fintype.card_le_of_injective rows hinj

/-- Aggregate an explicit pointwise Schur–Weyl estimate over diagrams whose
empirical spectrum is L1-separated. Both the analytic quadratic bound and
the polynomial number of diagrams are proved, while the representation
probability estimate is kept as an explicit premise. -/
theorem schur_tail_le {Λ : Type*} [Fintype Λ] [DecidableEq Λ] (r n : ℕ)
    (rows : Λ → Fin r → Fin (n + 1)) (hinj : Function.Injective rows)
    (reference : Fin r → ℝ) (frequency : Λ → Fin r → ℝ) (mass : Λ → ℝ)
    (href : ∀ i, 0 < reference i) (href1 : ∑ i, reference i = 1)
    (hfreq : ∀ a i, 0 ≤ frequency a i) (hfreq1 : ∀ a, ∑ i, frequency a i = 1)
    (hpointwise : ∀ a, mass a ≤ ((n : ℝ) + 1) ^ (r.choose 2) *
      Real.exp (-(n : ℝ) * kl (frequency a) reference))
    (bad : Finset Λ) (ε : ℝ) (hε : 0 ≤ ε)
    (hbad : ∀ a ∈ bad, ε ≤ l1 (frequency a) reference) :
    (∑ a ∈ bad, mass a) ≤ ((n : ℝ) + 1) ^ (r.choose 2 + r) *
      Real.exp (-(n : ℝ) * ε ^ 2 / 4) := by
  have hterm (a : Λ) (ha : a ∈ bad) : mass a ≤
      ((n : ℝ) + 1) ^ (r.choose 2) * Real.exp (-(n : ℝ) * ε ^ 2 / 4) := by
    have hk := l1_sq_div_four_le_kl (frequency a) reference (hfreq a) href (hfreq1 a) href1
    have hl : 0 ≤ l1 (frequency a) reference := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
    have hs := (sq_le_sq₀ hε hl).mpr (hbad a ha)
    have he : -(n : ℝ) * kl (frequency a) reference ≤ -(n : ℝ) * ε ^ 2 / 4 := by
      have hm := mul_le_mul_of_nonneg_left (show ε ^ 2 / 4 ≤ kl (frequency a) reference by linarith)
        (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
      nlinarith
    exact (hpointwise a).trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr he) (by positivity))
  have hcard : (bad.card : ℝ) ≤ ((n : ℝ) + 1) ^ r := by
    have hc := bad.card_le_univ.trans (diagram_card_le r n rows hinj)
    exact_mod_cast hc
  calc
    (∑ a ∈ bad, mass a) ≤ ∑ _a ∈ bad,
        ((n : ℝ) + 1) ^ (r.choose 2) * Real.exp (-(n : ℝ) * ε ^ 2 / 4) :=
      Finset.sum_le_sum hterm
    _ = (bad.card : ℝ) * (((n : ℝ) + 1) ^ (r.choose 2) *
        Real.exp (-(n : ℝ) * ε ^ 2 / 4)) := by simp
    _ ≤ ((n : ℝ) + 1) ^ r * (((n : ℝ) + 1) ^ (r.choose 2) *
        Real.exp (-(n : ℝ) * ε ^ 2 / 4)) :=
      mul_le_mul_of_nonneg_right hcard (by positivity)
    _ = _ := by rw [pow_add]; ring

/-- At logarithmic-over-square-root separation the actual bad mass is
bounded by the scalar concentration function already used by the proof. -/
theorem schur_tail_le_tailBound {Λ : Type*} [Fintype Λ] [DecidableEq Λ] (r n : ℕ)
    (hn : 2 ≤ n) (rows : Λ → Fin r → Fin (n + 1)) (hinj : Function.Injective rows)
    (reference : Fin r → ℝ) (frequency : Λ → Fin r → ℝ) (mass : Λ → ℝ)
    (href : ∀ i, 0 < reference i) (href1 : ∑ i, reference i = 1)
    (hfreq : ∀ a i, 0 ≤ frequency a i) (hfreq1 : ∀ a, ∑ i, frequency a i = 1)
    (hpointwise : ∀ a, mass a ≤ ((n : ℝ) + 1) ^ (r.choose 2) *
      Real.exp (-(n : ℝ) * kl (frequency a) reference))
    (bad : Finset Λ)
    (hbad : ∀ a ∈ bad, Real.logb 2 n / Real.sqrt n ≤ l1 (frequency a) reference) :
    (∑ a ∈ bad, mass a) ≤ Concentration.tailBound (r.choose 2 + r) n := by
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hs : Real.sqrt n ≠ 0 := (Real.sqrt_pos.mpr hn0).ne'
  have he : 0 ≤ Real.logb 2 n / Real.sqrt n := by
    apply div_nonneg
    · exact (Real.logb_pos (by norm_num) (by linarith : (1 : ℝ) < n)).le
    · exact Real.sqrt_nonneg _
  have h := schur_tail_le r n rows hinj reference frequency mass href href1 hfreq hfreq1
    hpointwise bad _ he hbad
  have hid : -(n : ℝ) * (Real.logb 2 n / Real.sqrt n) ^ 2 / 4 = -(Real.logb 2 n) ^ 2 / 4 := by
    rw [div_pow, Real.sq_sqrt hn0.le]
    field_simp
  simpa only [hid, Concentration.tailBound] using h

/-- Full classical atypical-mass estimate for supported integral diagrams.
The bounded-row injection and the actual failure of `Typical` discharge
the counting and separation hypotheses. Only the pointwise Schur–Weyl
probability formula remains external. -/
theorem schur_atypical_tail_le {d r : ℕ} (s : FixedSpectrum d r)
    {Λ : Type*} [Fintype Λ] [DecidableEq Λ] (n : ℕ) (hn : 2 ≤ n)
    (row : Λ → ℕ → ℤ) (mass : Λ → ℝ)
    (hinj : Function.Injective (fun a (i : Fin r) => row a i))
    (hrow0 : ∀ a i, i < r → 0 ≤ row a i)
    (hrown : ∀ a i, i < r → row a i ≤ (n : ℤ))
    (hzero : ∀ a i, r ≤ i → i < d → row a i = 0)
    (hsize : ∀ a, ∑ i : Fin r, row a i = (n : ℤ))
    (hpointwise : ∀ a, mass a ≤ ((n : ℝ) + 1) ^ (r.choose 2) * Real.exp
      (-(n : ℝ) * kl (rowFrequency r n (row a)) (fun i : Fin r => s.eigenvalue i))) :
    (∑ a ∈ Finset.univ.filter (fun a => ¬ TypicalRows.Typical s n (row a)), mass a) ≤
      Concentration.tailBound (r.choose 2 + r) n := by
  classical
  let code : Λ → Fin r → Fin (n + 1) := fun a i =>
    ⟨(row a i).toNat, by have h0 := hrow0 a i i.isLt; have h1 := hrown a i i.isLt; omega⟩
  have hc : Function.Injective code := by
    intro a b he
    apply hinj
    funext i
    have h := congrArg Fin.val (congrFun he i)
    change (row a i).toNat = (row b i).toNat at h
    have ha := hrow0 a i i.isLt
    have hb := hrow0 b i i.isLt
    change row a i = row b i
    omega
  apply schur_tail_le_tailBound r n hn code hc (fun i : Fin r => s.eigenvalue i)
    (fun a => rowFrequency r n (row a)) mass
    (fun i => s.positive i i.isLt)
    (by simpa only [Fin.sum_univ_eq_sum_range] using s.normalized)
    (fun a i => div_nonneg (by exact_mod_cast hrow0 a i i.isLt) (Nat.cast_nonneg _))
    (fun a => rowFrequency_normalized r n (by omega) (row a) (hsize a))
    hpointwise _ ?_
  intro a ha
  exact notTypical_l1_lower s n hn (row a) (hzero a) (hsize a) (Finset.mem_filter.mp ha).2

end FreeEntropy.FiniteConcentration
