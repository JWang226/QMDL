/-
Copyright (c) 2026 Free Entropy formalization contributors.
See LICENSE and NOTICE in the repository root for license and attribution.
-/

import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum

/-!
# The analytic part of the Weyl dimension asymptotic

This file proves a finite-product logarithmic asymptotic from convergence of
the normalized factors. Its specialization to the active roots of a Weyl
product is proved below. Identifying this product with the dimension of an
irreducible representation is a separate, unformalized representation theorem.
All logarithms in the conclusions are base two.
-/

noncomputable section
open Filter
open scoped BigOperators Topology

namespace FreeEntropy
namespace Weyl

/-- The paper's logarithmic error scale, with the value at zero immaterial. -/
def errorScale (n : ℕ) : ℝ := Real.logb 2 n / Real.sqrt n

theorem errorScale_tendsto_zero : Tendsto errorScale atTop (𝓝 0) := by
  have h := (isLittleO_log_rpow_atTop (r := (1 / 2 : ℝ)) (by norm_num)).tendsto_div_nhds_zero
  have hn := h.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  have hdiv := hn.div_const (Real.log 2)
  have hdiv' := hdiv
  simp only [zero_div] at hdiv'
  apply hdiv'.congr'
  filter_upwards [] with n
  dsimp [errorScale, Real.logb]
  rw [Real.sqrt_eq_rpow]
  ring

/-- Normalizing a fixed finite product by its polynomial degree commutes
with the product, including the empty product. -/
theorem normalized_product {ι : Type*} (s : Finset ι) (f : ι → ℝ) (t : ℝ) :
    (∏ i ∈ s, f i) / t ^ s.card = ∏ i ∈ s, f i / t := by
  rw [Finset.prod_div_distrib, Finset.prod_const]

/-- A finite collection of factors asymptotic to `n * slope i` has a
base-two logarithmic expansion, through the additive constant. -/
theorem log_product_asymptotic {ι : Type*} (s : Finset ι)
    (f : ℕ → ι → ℝ) (slope : ι → ℝ)
    (hpos : ∀ i ∈ s, 0 < slope i)
    (hlim : ∀ i ∈ s, Tendsto (fun n => f n i / (n : ℝ)) atTop (𝓝 (slope i))) :
    Tendsto (fun n => Real.logb 2 (∏ i ∈ s, f n i) -
      ((s.card : ℝ) * Real.logb 2 n + ∑ i ∈ s, Real.logb 2 (slope i)))
      atTop (𝓝 0) := by
  have hp : 0 < ∏ i ∈ s, slope i := Finset.prod_pos hpos
  have ht := tendsto_finset_prod s hlim
  have hlog := (Real.continuousAt_logb (b := 2) hp.ne').tendsto.comp ht
  have hc := hlog.sub_const (Real.logb 2 (∏ i ∈ s, slope i))
  simp only [sub_self] at hc
  apply hc.congr'
  have he : ∀ᶠ n in atTop, 0 < ∏ i ∈ s, f n i / (n : ℝ) :=
    ht.eventually (eventually_gt_nhds hp)
  filter_upwards [he, eventually_gt_atTop (0 : ℕ)] with n hn hn0
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn0.ne'
  have hf : (∏ i ∈ s, f n i) ≠ 0 := by
    intro hz
    rw [← normalized_product, hz, zero_div] at hn
    exact (lt_irrefl 0 hn)
  dsimp only [Function.comp_def]
  rw [← normalized_product, Real.logb_div hf (pow_ne_zero _ hn'), Real.logb_pow,
    Real.logb_prod s slope (fun i hi => (hpos i hi).ne')]
  ring

/-- The active positive roots: indices are zero based, and roots wholly
below the rank boundary contribute a factor exactly one. -/
def activeRoots (d r : ℕ) : Finset (ℕ × ℕ) :=
  (Finset.range r).biUnion (fun i => (Finset.Ico (i + 1) d).image (fun j => (i, j)))

@[simp] theorem mem_activeRoots {d r i j : ℕ} :
    (i, j) ∈ activeRoots d r ↔ i < r ∧ i < j ∧ j < d := by
  simp [activeRoots, and_assoc]

/-- The active portion of the exact Weyl product, as a real number. -/
def activeProduct (d r : ℕ) (row : ℕ → ℝ) : ℝ :=
  ∏ p ∈ activeRoots d r, (row p.1 - row p.2 + (p.2 - p.1 : ℕ)) / (p.2 - p.1 : ℕ)

/-- The leading expression in root-indexed form. Regrouping its terms gives
the eigenvalue differences and factorial denominator of `L_{d,r}`. -/
def rootLeading (d r : ℕ) (x : ℕ → ℝ) (n : ℕ) : ℝ :=
  ((activeRoots d r).card : ℝ) * Real.logb 2 n +
    ∑ p ∈ activeRoots d r, Real.logb 2 ((x p.1 - x p.2) / (p.2 - p.1 : ℕ))

theorem activeProduct_log_asymptotic (d r : ℕ) (row : ℕ → ℕ → ℝ)
    (x : ℕ → ℝ)
    (hgap : ∀ i j, i < r → i < j → j < d → x j < x i)
    (hrow : ∀ i, i < d → Tendsto (fun n => row n i / (n : ℝ)) atTop (𝓝 (x i))) :
    Tendsto (fun n => Real.logb 2 (activeProduct d r (row n)) - rootLeading d r x n)
      atTop (𝓝 0) := by
  apply log_product_asymptotic (activeRoots d r)
  · intro p hp
    obtain ⟨hi, hij, hj⟩ := mem_activeRoots.mp hp
    exact div_pos (sub_pos.mpr (hgap _ _ hi hij hj)) (by exact_mod_cast Nat.sub_pos_of_lt hij)
  · intro p hp
    obtain ⟨hi, hij, hj⟩ := mem_activeRoots.mp hp
    have hconst : Tendsto (fun n : ℕ => ((p.2 - p.1 : ℕ) : ℝ) / (n : ℝ))
        atTop (𝓝 0) := tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
    have h := (((hrow p.1 (hij.trans hj)).sub (hrow p.2 hj)).add hconst).div_const
      (((p.2 - p.1 : ℕ) : ℝ))
    simp only [add_zero] at h
    convert h using 1
    ext n
    dsimp
    ring

end Weyl
end FreeEntropy
