/-
Copyright (c) 2026 Free Entropy formalization contributors.
See LICENSE and NOTICE in the repository root for license and attribution.
-/

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The finite quantitative core of Theorem 2 (Cloning accuracy)

These results formalize the finite-support scalar estimates in the proof of
Theorem 2 of `article.tex`. The representation-theoretic construction of the
channels, the Casimir/projector estimate, and the operator trace comparison
are separated from this scalar file. `CartanChannel`, `ProjectorGeometry`,
and `CloningMatrices` now prove the matrix/channel bridges. Representation
weight and Casimir facts remain explicit inputs to the final reduction. A finite index type can contain the union of the two
representations' supported weights, extending multiplicities by zero.
-/

open scoped BigOperators

namespace FreeEntropy.Cloning

/-- The product estimate used with the factors of the Weyl dimension ratio. -/
theorem product_loss_le_sum {ι : Type*} (s : Finset ι) (a : ι → ℝ)
    (ha : ∀ i ∈ s, 0 ≤ a i) (ha1 : ∀ i ∈ s, a i ≤ 1) :
    0 ≤ 1 - ∏ i ∈ s, (1 - a i) ∧
      1 - ∏ i ∈ s, (1 - a i) ≤ ∑ i ∈ s, a i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    have hai := ha i (Finset.mem_insert_self i s)
    have hai1 := ha1 i (Finset.mem_insert_self i s)
    have ih' := ih (fun j hj => ha j (Finset.mem_insert_of_mem hj))
      (fun j hj => ha1 j (Finset.mem_insert_of_mem hj))
    have hp : 0 ≤ ∏ j ∈ s, (1 - a j) := by
      apply Finset.prod_nonneg
      intro j hj
      exact sub_nonneg.mpr (ha1 j (Finset.mem_insert_of_mem hj))
    simp only [Finset.prod_insert hi, Finset.sum_insert hi]
    constructor <;> nlinarith [mul_nonneg hai ih'.1]

/-- Scalar Weyl factors give a dimension deficit bounded by their increments.
No Weyl dimension formula is assumed implicitly: its right hand side is the
product appearing explicitly in this statement. -/
theorem weyl_product_deficit {ι : Type*} (s : Finset ι)
    (den inc : ι → ℝ)
    (hden : ∀ i ∈ s, 0 < den i) (hinc : ∀ i ∈ s, 0 ≤ inc i) :
    0 ≤ 1 - ∏ i ∈ s, den i / (den i + inc i) ∧
      1 - ∏ i ∈ s, den i / (den i + inc i) ≤ ∑ i ∈ s, inc i / den i := by
  have hsumden (i) (hi : i ∈ s) : 0 < den i + inc i := by
    linarith [hden i hi, hinc i hi]
  have hfactor (i) (hi : i ∈ s) :
      den i / (den i + inc i) = 1 - inc i / (den i + inc i) := by
    field_simp [ne_of_gt (hsumden i hi)]
    ring
  have h := product_loss_le_sum s (fun i => inc i / (den i + inc i))
    (fun i hi => div_nonneg (hinc i hi) (le_of_lt (hsumden i hi)))
    (fun i hi => (div_le_one (hsumden i hi)).mpr (by linarith [hden i hi]))
  have hp : (∏ i ∈ s, den i / (den i + inc i)) =
      ∏ i ∈ s, (1 - inc i / (den i + inc i)) :=
    Finset.prod_congr rfl hfactor
  rw [hp]
  refine ⟨h.1, h.2.trans ?_⟩
  apply Finset.sum_le_sum
  intro i hi
  exact div_le_div_of_nonneg_left (hinc i hi) (hden i hi)
    (by linarith [hinc i hi])

/-- If every Weyl increment is at most `D` and every denominator with
nonzero increment is at least `b+1`, the dimension loss is at most the
number of factors times `D/(b+1)`. The zero-increment alternative handles
the pairs of rows beyond the support in the rank-deficient case. -/
theorem weyl_product_deficit_le_card {ι : Type*} (s : Finset ι)
    (den inc : ι → ℝ) (b D : ℝ) (hb : 0 ≤ b)
    (hden0 : ∀ i ∈ s, 0 < den i)
    (hden : ∀ i ∈ s, inc i = 0 ∨ b + 1 ≤ den i)
    (hinc : ∀ i ∈ s, 0 ≤ inc i) (hincD : ∀ i ∈ s, inc i ≤ D) :
    1 - ∏ i ∈ s, den i / (den i + inc i) ≤
      (s.card : ℝ) * D / (b + 1) := by
  have hb1 : 0 < b + 1 := by linarith
  calc
    _ ≤ ∑ i ∈ s, inc i / den i := (weyl_product_deficit s den inc hden0 hinc).2
    _ ≤ ∑ _i ∈ s, D / (b + 1) := by
      apply Finset.sum_le_sum
      intro i hi
      by_cases hzero : inc i = 0
      · rw [hzero, zero_div]
        exact div_nonneg ((hinc i hi).trans (hincD i hi)) (le_of_lt hb1)
      have hdeni := (hden i hi).resolve_left hzero
      calc
        _ ≤ inc i / (b + 1) := div_le_div_of_nonneg_left (hinc i hi) hb1 hdeni
        _ ≤ D / (b + 1) := div_le_div_of_nonneg_right (hincD i hi) (le_of_lt hb1)
    _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]; ring

/-- The finite Markov estimate used to control deep weight sectors. -/
theorem tail_mass_le_mean_div {ι : Type*} (s : Finset ι)
    (depth mass : ι → ℝ) (B K : ℝ)
    (hB : 0 < B) (hmass : ∀ i ∈ s, 0 ≤ mass i)
    (hdepth : ∀ i ∈ s, 0 ≤ depth i)
    (hmean : ∑ i ∈ s, depth i * mass i ≤ K) :
    ∑ i ∈ s with B ≤ depth i, mass i ≤ K / B := by
  classical
  apply (le_div_iff₀ hB).mpr
  calc
    (∑ i ∈ s with B ≤ depth i, mass i) * B =
        ∑ i ∈ s with B ≤ depth i, mass i * B := Finset.sum_mul _ _ _
    _ ≤ ∑ i ∈ s with B ≤ depth i, depth i * mass i := by
      apply Finset.sum_le_sum
      intro i hi
      obtain ⟨his, hiB⟩ := Finset.mem_filter.mp hi
      nlinarith [hmass i his]
    _ ≤ ∑ i ∈ s, depth i * mass i := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      intro i hi _
      exact mul_nonneg (hdepth i hi) (hmass i hi)
    _ ≤ K := hmean

/-- The eigenvalue ratio estimate from normalization, monotone multiplicities,
equality at shallow depths, and a uniform mean-depth bound. -/
theorem eigenvalue_ratio_deficit {ι : Type*} (s : Finset ι)
    (depth m n : ι → ℕ) (p q : ι → ℝ) (Z K : ℝ) (g : ℕ)
    (hq : ∀ i ∈ s, 0 ≤ q i)
    (hmn : ∀ i ∈ s, m i ≤ n i)
    (hshallow : ∀ i ∈ s, depth i ≤ g → m i = n i)
    (hp_norm : ∑ i ∈ s, p i * (m i : ℝ) = 1)
    (hq_norm : ∑ i ∈ s, q i * (n i : ℝ) = 1)
    (hratio : ∀ i ∈ s, q i = Z * p i)
    (hmean : ∑ i ∈ s, (depth i : ℝ) * q i * (n i : ℝ) ≤ K) :
    0 ≤ 1 - Z ∧ 1 - Z ≤ K / ((g : ℝ) + 1) := by
  have hq_m : ∑ i ∈ s, q i * (m i : ℝ) = Z := by
    calc
      _ = ∑ i ∈ s, Z * (p i * (m i : ℝ)) := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [hratio i hi]
        ring
      _ = Z * (∑ i ∈ s, p i * (m i : ℝ)) := (Finset.mul_sum _ _ _).symm
      _ = Z := by rw [hp_norm]; ring
  have hidentity : ∑ i ∈ s, q i * ((n i : ℝ) - (m i : ℝ)) = 1 - Z := by
    simp_rw [mul_sub]
    rw [Finset.sum_sub_distrib, hq_norm, hq_m]
  have hnonneg : 0 ≤ ∑ i ∈ s, q i * ((n i : ℝ) - (m i : ℝ)) := by
    apply Finset.sum_nonneg
    intro i hi
    exact mul_nonneg (hq i hi) (sub_nonneg.mpr (by exact_mod_cast hmn i hi))
  refine ⟨by rwa [hidentity] at hnonneg, ?_⟩
  apply (le_div_iff₀ (by positivity : 0 < (g : ℝ) + 1)).mpr
  rw [← hidentity, Finset.sum_mul]
  calc
    _ ≤ ∑ i ∈ s, (depth i : ℝ) * q i * (n i : ℝ) := by
      apply Finset.sum_le_sum
      intro i hi
      by_cases hsh : depth i ≤ g
      · rw [hshallow i hi hsh]
        simp only [sub_self, mul_zero, zero_mul]
        exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (hq i hi)) (Nat.cast_nonneg _)
      · have hdeep : g + 1 ≤ depth i := by omega
        have hdeepR : (g : ℝ) + 1 ≤ (depth i : ℝ) := by exact_mod_cast hdeep
        have hnm : (m i : ℝ) ≤ (n i : ℝ) := by exact_mod_cast hmn i hi
        have hqi := hq i hi
        have hm0 : 0 ≤ (m i : ℝ) := Nat.cast_nonneg _
        have hn0 : 0 ≤ (n i : ℝ) := Nat.cast_nonneg _
        have hg0 : 0 ≤ (g : ℝ) + 1 := by positivity
        calc
          _ ≤ (q i * (n i : ℝ)) * ((g : ℝ) + 1) := by
            exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
              (by linarith) hqi) hg0
          _ ≤ (q i * (n i : ℝ)) * (depth i : ℝ) :=
            mul_le_mul_of_nonneg_left hdeepR (mul_nonneg hqi hn0)
          _ = _ := by ring
    _ ≤ K := hmean

/-- Integrality makes the capped error equal to one beyond the shallow range. -/
theorem deficit_cap_eq_one_of_deep (depth g : ℕ) (D : ℝ)
    (hD : 1 ≤ D) (hdeep : g < depth) :
    min 1 (2 * (depth : ℝ) * D / ((g : ℝ) + 2)) = 1 := by
  apply min_eq_left
  apply (le_div_iff₀ (by positivity : 0 < (g : ℝ) + 2)).mpr
  have hd : (g : ℝ) + 1 ≤ (depth : ℝ) := by exact_mod_cast (Nat.succ_le_of_lt hdeep)
  have hg : 0 ≤ (g : ℝ) := Nat.cast_nonneg _
  nlinarith

/-- Averaging the pointwise capped Casimir bound requires only the mean depth. -/
theorem averaged_deficit_le {ι : Type*} (s : Finset ι)
    (depth mass : ι → ℝ) (D g K : ℝ)
    (hD : 0 ≤ D) (hg : 0 ≤ g)
    (hmass : ∀ i ∈ s, 0 ≤ mass i)
    (hmean : ∑ i ∈ s, depth i * mass i ≤ K) :
    ∑ i ∈ s, min 1 (2 * depth i * D / (g + 2)) * mass i ≤
      2 * D * K / (g + 2) := by
  have hcoef : 0 ≤ 2 * D / (g + 2) := by positivity
  calc
    _ ≤ ∑ i ∈ s, (2 * depth i * D / (g + 2)) * mass i := by
      exact Finset.sum_le_sum fun i hi =>
        mul_le_mul_of_nonneg_right (min_le_right _ _) (hmass i hi)
    _ = (2 * D / (g + 2)) * ∑ i ∈ s, depth i * mass i := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ ≤ (2 * D / (g + 2)) * K := mul_le_mul_of_nonneg_left hmean hcoef
    _ = _ := by ring

/-- The final scalar collection step of Theorem 2 for nonzero dominant
difference. `Ef` and `Er` denote the actual errors only after the unformalized
channel estimates have been supplied as `hf` and `hr`.

`N` represents `Nat.choose d 2`; `K` represents the spectrum-dependent
mean-depth constant. The forward estimate is slightly sharper than the
common constant subsequently used in the paper. -/
theorem cloning_bounds_of_deficits
    (b g D N K Ef Er dimRatio Z Mμ Mν : ℝ)
    (hb : 0 ≤ b) (hbg : b ≤ g) (hD : 1 ≤ D)
    (hK : 0 ≤ K)
    (hf : Ef ≤ 1 - dimRatio + Mν) (hr : Er ≤ 1 - Z + Mμ)
    (hdim : 1 - dimRatio ≤ N * D / (b + 1))
    (hZ : 1 - Z ≤ K / (g + 1))
    (hMμ : Mμ ≤ 2 * D * K / (g + 2))
    (hMν : Mν ≤ 2 * D * K / (g + 2)) :
    Ef ≤ (N + 2 * K) * D / (b + 1) ∧
      Er ≤ 3 * K * D / (b + 1) := by
  have hb1 : 0 < b + 1 := by linarith
  have hnum : 0 ≤ 2 * D * K := by positivity
  have hM : 2 * D * K / (g + 2) ≤ 2 * D * K / (b + 1) :=
    div_le_div_of_nonneg_left hnum hb1 (by linarith)
  have hZ' : K / (g + 1) ≤ K * D / (b + 1) := by
    calc
      _ ≤ K / (b + 1) := div_le_div_of_nonneg_left hK hb1 (by linarith)
      _ ≤ K * D / (b + 1) := by
        apply div_le_div_of_nonneg_right _ (le_of_lt hb1)
        nlinarith
  constructor
  · calc
      Ef ≤ N * D / (b + 1) + 2 * D * K / (b + 1) :=
        hf.trans (add_le_add hdim (hMν.trans hM))
      _ = _ := by ring
  · calc
      Er ≤ K * D / (b + 1) + 2 * D * K / (b + 1) :=
        hr.trans (add_le_add (hZ.trans hZ') (hMμ.trans hM))
      _ = _ := by ring

/-- A uniform common constant for the two directions. -/
theorem common_cloning_constant (b D N K Ef Er : ℝ)
    (hb : 0 ≤ b) (hD : 0 ≤ D) (hN : 0 ≤ N) (hK : 0 ≤ K)
    (hf : Ef ≤ (N + 2 * K) * D / (b + 1))
    (hr : Er ≤ 3 * K * D / (b + 1)) :
    Ef ≤ (N + 3 * K) * D / (b + 1) ∧
      Er ≤ (N + 3 * K) * D / (b + 1) := by
  constructor
  · apply hf.trans
    apply div_le_div_of_nonneg_right _ (by linarith)
    nlinarith
  · apply hr.trans
    apply div_le_div_of_nonneg_right _ (by linarith)
    nlinarith

/-- A finite sum of the capped block errors used in the paper. -/
noncomputable def blockDeficit {ι : Type*} (s : Finset ι)
    (depth m : ι → ℕ) (p : ι → ℝ) (D g : ℕ) : ℝ :=
  ∑ i ∈ s, min 1 (2 * (depth i : ℝ) * (D : ℝ) / ((g : ℝ) + 2)) *
    (p i * (m i : ℝ))

/-- Rank-one supported sectors have depth zero, so their projector deficit
vanishes identically. -/
theorem blockDeficit_eq_zero_of_depth_zero {ι : Type*} (s : Finset ι)
    (depth m : ι → ℕ) (p : ι → ℝ) (D g : ℕ)
    (hdepth : ∀ i ∈ s, depth i = 0) : blockDeficit s depth m p D g = 0 := by
  unfold blockDeficit
  apply Finset.sum_eq_zero
  intro i hi
  simp [hdepth i hi]

/-- The separate rank-one conclusion: a Weyl dimension loss in the forward
direction and a zero upper bound for the reverse error. For a nonnegative
trace distance, this upper bound implies that the error is zero. -/
theorem rank_one_cloning_bounds {ι : Type*} (s : Finset ι)
    (depth m n : ι → ℕ) (p q : ι → ℝ) (D g : ℕ)
    (b N Ef Er dimRatio Z : ℝ)
    (hdepth : ∀ i ∈ s, depth i = 0) (hZ : Z = 1)
    (hdim : 1 - dimRatio ≤ N * (D : ℝ) / (b + 1))
    (hf : Ef ≤ 1 - dimRatio + blockDeficit s depth n q D g)
    (hr : Er ≤ 1 - Z + blockDeficit s depth m p D g) :
    Ef ≤ N * (D : ℝ) / (b + 1) ∧ Er ≤ 0 := by
  rw [blockDeficit_eq_zero_of_depth_zero s depth n q D g hdepth, add_zero] at hf
  rw [blockDeficit_eq_zero_of_depth_zero s depth m p D g hdepth, hZ] at hr
  exact ⟨hf.trans hdim, by linarith⟩

/-- Theorem 2's scalar proof on a finite family of weight blocks, including
the zero-difference case.

The unproved quantum/representation input is visible in the hypotheses:
the two channel-error comparisons, the Weyl dimension loss, monotonicity
and shallow equality of multiplicities, and the uniform mean bounds.
Normalization, the scalar eigenvalue relation, averaging, tail control,
and assembling the common constant are checked in this theorem. This is a
conditional reduction, not a construction of the generalized channels.

For rank one, `rank_one_cloning_bounds` separately preserves the sharper
zero upper bound for the reverse error. -/
theorem cloning_accuracy_of_finite_blocks {ι : Type*} (s : Finset ι)
    (depth m n : ι → ℕ) (p q : ι → ℝ) (D g : ℕ)
    (b N K Ef Er dimRatio Z : ℝ)
    (hb : 0 ≤ b) (hbg : b ≤ (g : ℝ)) (hN : 0 ≤ N) (hK : 0 ≤ K)
    (hp : ∀ i ∈ s, 0 ≤ p i) (hq : ∀ i ∈ s, 0 ≤ q i)
    (hmn : ∀ i ∈ s, m i ≤ n i)
    (hshallow : ∀ i ∈ s, depth i ≤ g → m i = n i)
    (hp_norm : ∑ i ∈ s, p i * (m i : ℝ) = 1)
    (hq_norm : ∑ i ∈ s, q i * (n i : ℝ) = 1)
    (hratio : ∀ i ∈ s, q i = Z * p i)
    (hp_mean : ∑ i ∈ s, (depth i : ℝ) * p i * (m i : ℝ) ≤ K)
    (hq_mean : ∑ i ∈ s, (depth i : ℝ) * q i * (n i : ℝ) ≤ K)
    (hdim : 1 - dimRatio ≤ N * (D : ℝ) / (b + 1))
    (hzero : D = 0 → Ef = 0 ∧ Er = 0)
    (hf : Ef ≤ 1 - dimRatio + blockDeficit s depth n q D g)
    (hr : Er ≤ 1 - Z + blockDeficit s depth m p D g) :
    Ef ≤ (N + 3 * K) * (D : ℝ) / (b + 1) ∧
      Er ≤ (N + 3 * K) * (D : ℝ) / (b + 1) := by
  by_cases hD0 : D = 0
  · obtain ⟨hf0, hr0⟩ := hzero hD0
    simp [hD0, hf0, hr0]
  have hD : (1 : ℝ) ≤ (D : ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr hD0
  have hZ := (eigenvalue_ratio_deficit s depth m n p q Z K g hq hmn
    hshallow hp_norm hq_norm hratio hq_mean).2
  have hMp : blockDeficit s depth m p D g ≤ 2 * (D : ℝ) * K / ((g : ℝ) + 2) := by
    apply averaged_deficit_le s (fun i => (depth i : ℝ))
      (fun i => p i * (m i : ℝ)) (D : ℝ) (g : ℝ) K
      (Nat.cast_nonneg _) (Nat.cast_nonneg _)
      (fun i hi => mul_nonneg (hp i hi) (Nat.cast_nonneg _))
    simpa only [mul_assoc] using hp_mean
  have hMq : blockDeficit s depth n q D g ≤ 2 * (D : ℝ) * K / ((g : ℝ) + 2) := by
    apply averaged_deficit_le s (fun i => (depth i : ℝ))
      (fun i => q i * (n i : ℝ)) (D : ℝ) (g : ℝ) K
      (Nat.cast_nonneg _) (Nat.cast_nonneg _)
      (fun i hi => mul_nonneg (hq i hi) (Nat.cast_nonneg _))
    simpa only [mul_assoc] using hq_mean
  have hsharp := cloning_bounds_of_deficits b (g : ℝ) (D : ℝ) N K Ef Er
    dimRatio Z (blockDeficit s depth m p D g) (blockDeficit s depth n q D g)
    hb hbg hD hK hf hr hdim hZ hMp hMq
  exact common_cloning_constant b (D : ℝ) N K Ef Er hb (Nat.cast_nonneg _)
    hN hK hsharp.1 hsharp.2

end FreeEntropy.Cloning
