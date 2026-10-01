/-
Copyright (c) 2026 Free Entropy formalization contributors.
See LICENSE and NOTICE in the repository root for license and attribution.
-/

import FreeEntropy.Weyl
import FreeEntropy.WeylCombinatorics
import FreeEntropy.Protocol
import FreeEntropy.Concentration
import FreeEntropy.OptimalMemory
import FreeEntropy.Cloning
import Mathlib.Analysis.Asymptotics.Lemmas

/-!
# Conditional analytic reductions of Theorems 1 and 2

These declarations deliberately say `of_estimates`: they prove the analytic
conclusions from explicit numerical consequences of the quantum constructions.
They do not claim that abstract real errors are trace distances of constructed
CPTP channels. See README.md for the missing representation/quantum bridges.
-/

noncomputable section
open Filter
open scoped Topology BigOperators
namespace FreeEntropy

/-- Exactly the typicality width used in the manuscript (base-two log). -/
def typicalWidth (n : ℕ) : ℝ := Real.sqrt ((n : ℝ) / 2) * Real.logb 2 n

theorem typicalWidth_div_tendsto_zero :
    Tendsto (fun n => typicalWidth n / (n : ℝ)) atTop (𝓝 0) := by
  have h := Weyl.errorScale_tendsto_zero.div_const (Real.sqrt 2)
  simp only [zero_div] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hs : Real.sqrt n ≠ 0 := (Real.sqrt_pos.mpr hn0).ne'
  have hs2 : Real.sqrt (2 : ℝ) ≠ 0 := (Real.sqrt_pos.mpr (by norm_num)).ne'
  dsimp [typicalWidth, Weyl.errorScale]
  rw [Real.sqrt_div hn0.le]
  field_simp
  rw [Real.sq_sqrt hn0.le]

/-- Ceiling and sublinear padding preserve each normalized row limit. -/
theorem paddedRow_normalized_tendsto (x k : ℝ) {ε : ℕ → ℝ}
    (hε : Tendsto (fun n => ε n / (n : ℝ)) atTop (𝓝 0)) :
    Tendsto (fun n : ℕ => (paddedRow n x (ε n) k : ℝ) / (n : ℝ)) atTop (𝓝 x) := by
  have hinv : Tendsto (fun n : ℕ => 1 / (n : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  have hlow : Tendsto
      (fun n : ℕ => ((n : ℝ) * x + k * (2 * ε n + 1)) / n) atTop (𝓝 x) := by
    have h := (tendsto_const_nhds (x := x)).add ((hε.const_mul 2).add hinv |>.const_mul k)
    simp only [mul_zero, add_zero] at h
    apply h.congr'
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
    have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
    field_simp
  have hupp := hlow.add hinv
  simp only [add_zero] at hupp
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow hupp
  · filter_upwards [] with n
    exact div_le_div_of_nonneg_right (Int.le_ceil _) (Nat.cast_nonneg _)
  · filter_upwards [] with n
    rw [← add_div]
    exact div_le_div_of_nonneg_right (Int.ceil_lt_add_one _).le (Nat.cast_nonneg _)

/-- From the paper's finite error envelope, obtain both its stated rate and
vanishing error. Sanov/Pinsker supplies `herror`, not a hidden axiom here. -/
theorem achieving_error_of_estimates (δ : ℕ → ℝ) (C : ℝ) (k : ℕ)
    (hδ0 : ∀ᶠ n in atTop, 0 ≤ δ n)
    (herror : ∀ᶠ n in atTop,
      δ n ≤ 2 * (C * Weyl.errorScale n) + 2 * Concentration.tailBound k n) :
    Asymptotics.IsBigO atTop δ Weyl.errorScale ∧ Tendsto δ atTop (𝓝 0) := by
  have hrate : ∀ᶠ n in atTop, 0 ≤ Weyl.errorScale n := by
    filter_upwards [eventually_ge_atTop (2 : ℕ)] with n hn
    have hn' : (1 : ℝ) < n := by exact_mod_cast (lt_of_lt_of_le (by decide : 1 < 2) hn)
    exact div_nonneg (Real.logb_pos (by norm_num) hn').le (Real.sqrt_nonneg _)
  have hbig : Asymptotics.IsBigO atTop δ Weyl.errorScale :=
    Protocol.error_isBigO (C := C) (T := 1) hδ0 hrate herror
      (Eventually.of_forall (fun _ => le_rfl))
      (by simpa [Weyl.errorScale] using Concentration.tailBound_eventually_le_errorScale k)
  exact ⟨hbig, hbig.trans_tendsto Weyl.errorScale_tendsto_zero⟩

/-- Achievability's analytic conclusion with actual natural memory
dimensions. The external inputs are the Weyl dimension identity and the
finite error envelope; no code existence theorem is asserted. -/
theorem theorem1_achievability_of_estimates
    (d r : ℕ) (row : ℕ → ℕ → ℝ) (x : ℕ → ℝ)
    (memory : ℕ → ℕ) (δ : ℕ → ℝ) (C : ℝ) (k : ℕ)
    (hgap : ∀ i j, i < r → i < j → j < d → x j < x i)
    (hrow : ∀ i, i < d → Tendsto (fun n => row n i / (n : ℝ)) atTop (𝓝 (x i)))
    (hdim : ∀ᶠ n in atTop, (memory n : ℝ) = Weyl.activeProduct d r (row n))
    (hδ0 : ∀ᶠ n in atTop, 0 ≤ δ n)
    (herror : ∀ᶠ n in atTop,
      δ n ≤ 2 * (C * Weyl.errorScale n) + 2 * Concentration.tailBound k n) :
    Tendsto (fun n => Real.logb 2 (memory n) - Weyl.rootLeading d r x n) atTop (𝓝 0) ∧
      Asymptotics.IsBigO atTop δ Weyl.errorScale ∧ Tendsto δ atTop (𝓝 0) := by
  refine ⟨?_, achieving_error_of_estimates δ C k hδ0 herror⟩
  apply (Weyl.activeProduct_log_asymptotic d r row x hgap hrow).congr'
  filter_upwards [hdim] with n hn
  rw [hn]

/-- Theorem 1's converse after the finite quantum-memory estimate and Weyl
identity have been supplied. The conclusion uses extended-real liminf, so
unbounded memory overheads are included. -/
theorem theorem1_converse_of_estimates
    (d r : ℕ) (row : ℕ → ℕ → ℝ) (x : ℕ → ℝ)
    (memory target : ℕ → ℕ) (δ e : ℕ → ℝ) (γ : ℝ)
    (hgap : ∀ i j, i < r → i < j → j < d → x j < x i)
    (hrow : ∀ i, i < d → Tendsto (fun n => row n i / (n : ℝ)) atTop (𝓝 (x i)))
    (hdim : ∀ᶠ n in atTop, (target n : ℝ) = Weyl.activeProduct d r (row n))
    (htarget : ∀ n, 0 < target n) (hγ : 0 < γ)
    (hδ : Tendsto δ atTop (𝓝 0))
    (he : Asymptotics.IsBigO atTop e Weyl.errorScale)
    (hbound : ∀ᶠ n in atTop,
      (target n : ℝ) * (1 - (δ n + e n) / γ) ≤ memory n) :
    (0 : EReal) ≤ liminf
      (fun n => ((Real.logb 2 (memory n) - Weyl.rootLeading d r x n : ℝ) : EReal)) atTop := by
  apply optimal_memory_converse hγ htarget hδ (he.trans_tendsto Weyl.errorScale_tendsto_zero)
    (hbound := hbound)
  apply (Weyl.activeProduct_log_asymptotic d r row x hgap hrow).congr'
  filter_upwards [hdim] with n hn
  rw [hn]

end FreeEntropy
