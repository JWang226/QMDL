/-
Copyright (c) 2026 Free Entropy formalization contributors.
See LICENSE and NOTICE in the repository root for license and attribution.
-/

import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

/-!
# Decay of the concentration bound

Sanov/Pinsker and the Schur--Weyl distribution are not formalized here. This
file checks what happens to the explicit scalar upper bound once supplied.
-/

noncomputable section
open Filter
open scoped Topology
namespace FreeEntropy.Concentration

def tailBound (k n : ℕ) : ℝ :=
  ((n : ℝ) + 1) ^ k * Real.exp (-(Real.logb 2 n) ^ 2 / 4)

/-- A quantitative threshold after which the displayed Sanov bound is at
most `1/n`; fixed polynomial prefactors are absorbed by the squared log. -/
theorem tailBound_le_inv (k n : ℕ) (hn : 2 ≤ n)
    (hlarge : 4 * (2 * (k : ℝ) + 1) * Real.log 2 ≤ Real.logb 2 n) :
    tailBound k n ≤ 1 / (n : ℝ) := by
  have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hln : Real.log 2 ≤ Real.log n := Real.log_le_log (by norm_num) hn'
  have hlog : Real.log ((n : ℝ) + 1) ≤ 2 * Real.log n := by
    calc
      _ ≤ Real.log (2 * (n : ℝ)) := Real.log_le_log (by positivity) (by linarith)
      _ = Real.log 2 + Real.log n := Real.log_mul (by norm_num) hn0.ne'
      _ ≤ 2 * Real.log n := by linarith
  have hb : 0 ≤ Real.logb 2 n := (Real.logb_pos (by norm_num) (by linarith : (1 : ℝ) < n)).le
  have hbmul : Real.logb 2 n * Real.log 2 = Real.log n := by
    unfold Real.logb
    exact div_mul_cancel₀ _ hl2.ne'
  have hquad := mul_le_mul_of_nonneg_right hlarge hb
  have hexp : (k : ℝ) * Real.log ((n : ℝ) + 1) - (Real.logb 2 n) ^ 2 / 4 ≤
      -Real.log n := by
    have hk := mul_le_mul_of_nonneg_left hlog (Nat.cast_nonneg k)
    nlinarith [hbmul]
  calc
    tailBound k n = Real.exp ((k : ℝ) * Real.log ((n : ℝ) + 1) -
        (Real.logb 2 n) ^ 2 / 4) := by
      unfold tailBound
      rw [Real.exp_sub, Real.exp_nat_mul, Real.exp_log (by positivity)]
      rw [neg_div]
      rw [Real.exp_neg]
      ring
    _ ≤ Real.exp (-Real.log n) := Real.exp_le_exp.mpr hexp
    _ = 1 / (n : ℝ) := by rw [Real.exp_neg, Real.exp_log hn0, one_div]

theorem tailBound_eventually_le_inv (k : ℕ) :
    ∀ᶠ n in atTop, tailBound k n ≤ 1 / (n : ℝ) := by
  have hlog : Tendsto (fun n : ℕ => Real.logb 2 n) atTop atTop :=
    (Real.tendsto_logb_atTop (by norm_num : (1 : ℝ) < 2)).comp tendsto_natCast_atTop_atTop
  filter_upwards [eventually_ge_atTop 2,
    hlog.eventually (eventually_ge_atTop (4 * (2 * (k : ℝ) + 1) * Real.log 2))] with n hn hl
  exact tailBound_le_inv k n hn hl

theorem inv_le_errorScale (n : ℕ) (hn : 2 ≤ n) :
    1 / (n : ℝ) ≤ Real.logb 2 n / Real.sqrt n := by
  have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hs : 0 < Real.sqrt n := Real.sqrt_pos.mpr hn0
  have hsle : Real.sqrt n ≤ n := by
    apply (Real.sqrt_le_iff).mpr
    exact ⟨hn0.le, by nlinarith⟩
  have hl : 1 ≤ Real.logb 2 n := by
    simpa using Real.logb_le_logb_of_le (b := 2) (by norm_num) (by norm_num : (0 : ℝ) < 2) hn'
  exact (one_div_le_one_div_of_le hs hsle).trans (div_le_div_of_nonneg_right hl hs.le)

theorem tailBound_eventually_le_errorScale (k : ℕ) :
    ∀ᶠ n in atTop, tailBound k n ≤ Real.logb 2 n / Real.sqrt n := by
  filter_upwards [tailBound_eventually_le_inv k, eventually_ge_atTop 2] with n ht hn
  exact ht.trans (inv_le_errorScale n hn)

end FreeEntropy.Concentration
