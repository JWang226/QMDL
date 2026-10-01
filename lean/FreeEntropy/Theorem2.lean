/-
Copyright (c) 2026 Free Entropy formalization contributors.
See LICENSE and NOTICE in the repository root for license and attribution.
-/

import FreeEntropy.Cloning
import FreeEntropy.MeanDepth

/-!
# Theorem 2: explicit-constant reduction

This file is the scalar reduction, retained as a reusable intermediate step.
`CloningMatrices` derives its two error comparisons for actual CPTP outputs;
`CloningFromRows.theorem2_from_rows` also discharges the Weyl dimension-loss
inequality. Representation-specific weight and Casimir inputs remain explicit.

The main theorem covers `r ≥ 2`, including `D = 0`. The rank-one theorem
records the sharper reverse bound and makes its nonnegativity explicit.
-/

open scoped BigOperators

namespace FreeEntropy.Theorem2

open Cloning MeanDepth

/-- The spectrum/dimension constant chosen at the end of Theorem 2. -/
noncomputable def cloningConstant (d r : ℕ) (q : ℝ) : ℝ :=
  (d.choose 2 : ℝ) + 3 * meanDepthConstant (r.choose 2) q

theorem cloningConstant_nonneg (d r : ℕ) (q : ℝ) (hq : 0 ≤ q) (hq1 : q < 1) :
    0 ≤ cloningConstant d r q := by
  unfold cloningConstant
  exact add_nonneg (Nat.cast_nonneg _) (mul_nonneg (by norm_num)
    (meanDepthConstant_nonneg _ _ hq hq1))

/-- The quantitative content of Theorem 2, conditional on its remaining
representation/operator inputs. Unlike `cloning_accuracy_of_finite_blocks`,
this theorem does not assume uniform mean-depth bounds: it derives both
from the multiplicity envelopes and spectral decay, with the exact
constant `choose(d,2) + 3*N*q/(1-q)^(N+1)`, `N = choose(r,2)`.

The finite set `s` can contain the union of supported weight offsets,
extending multiplicities by zero outside each representation. -/
theorem theorem2_finite_reduction {ι : Type*} (s : Finset ι)
    (depth m n : ι → ℕ) (pμ pν : ι → ℝ) (d r D g : ℕ)
    (b q Ef Er dimRatio Z : ℝ)
    (hrank : 2 ≤ r) (hq : 0 ≤ q) (hq1 : q < 1)
    (hb : 0 ≤ b) (hbg : b ≤ (g : ℝ))
    (hpμ : ∀ i ∈ s, 0 ≤ pμ i) (hpν : ∀ i ∈ s, 0 ≤ pν i)
    (hmn : ∀ i ∈ s, m i ≤ n i)
    (hshallow : ∀ i ∈ s, depth i ≤ g → m i = n i)
    (hμ_norm : ∑ i ∈ s, pμ i * (m i : ℝ) = 1)
    (hν_norm : ∑ i ∈ s, pν i * (n i : ℝ) = 1)
    (hratio : ∀ i ∈ s, pν i = Z * pμ i)
    (hμ_spectral : ∀ i ∈ s, pμ i ≤ q ^ depth i)
    (hν_spectral : ∀ i ∈ s, pν i ≤ q ^ depth i)
    (hμ_mult : ∀ t, ∑ i ∈ s with depth i = t, m i ≤
      (t + r.choose 2 - 1).choose (r.choose 2 - 1))
    (hν_mult : ∀ t, ∑ i ∈ s with depth i = t, n i ≤
      (t + r.choose 2 - 1).choose (r.choose 2 - 1))
    (hdim : 1 - dimRatio ≤ (d.choose 2 : ℝ) * (D : ℝ) / (b + 1))
    (hzero : D = 0 → Ef = 0 ∧ Er = 0)
    (hf : Ef ≤ 1 - dimRatio + blockDeficit s depth n pν D g)
    (hr : Er ≤ 1 - Z + blockDeficit s depth m pμ D g) :
    Ef ≤ cloningConstant d r q * (D : ℝ) / (b + 1) ∧
      Er ≤ cloningConstant d r q * (D : ℝ) / (b + 1) := by
  have hN : 0 < r.choose 2 := Nat.choose_pos hrank
  have hK := meanDepthConstant_nonneg (r.choose 2) q hq hq1
  have hμ_mean := weight_mean_le s depth m pμ (r.choose 2) hN q hq hq1
    hμ_spectral hμ_mult
  have hν_mean := weight_mean_le s depth n pν (r.choose 2) hN q hq hq1
    hν_spectral hν_mult
  exact cloning_accuracy_of_finite_blocks s depth m n pμ pν D g b (d.choose 2 : ℝ)
    (meanDepthConstant (r.choose 2) q) Ef Er dimRatio Z hb hbg (Nat.cast_nonneg _) hK
    hpμ hpν hmn hshallow hμ_norm hν_norm hratio hμ_mean hν_mean hdim hzero hf hr

/-- Rank one retains a sharper conclusion than the common two-direction
bound: the reverse error is zero, provided `Er` is nonnegative. The
representation-specific inputs `hdepth` and `hZ` remain explicit. -/
theorem theorem2_rank_one {ι : Type*} (s : Finset ι)
    (depth m n : ι → ℕ) (pμ pν : ι → ℝ) (d D g : ℕ)
    (b Ef Er dimRatio Z : ℝ)
    (hdepth : ∀ i ∈ s, depth i = 0) (hZ : Z = 1) (hEr : 0 ≤ Er)
    (hdim : 1 - dimRatio ≤ (d.choose 2 : ℝ) * (D : ℝ) / (b + 1))
    (hf : Ef ≤ 1 - dimRatio + blockDeficit s depth n pν D g)
    (hr : Er ≤ 1 - Z + blockDeficit s depth m pμ D g) :
    Ef ≤ cloningConstant d 1 0 * (D : ℝ) / (b + 1) ∧ Er = 0 := by
  have h := rank_one_cloning_bounds s depth m n pμ pν D g b (d.choose 2 : ℝ)
    Ef Er dimRatio Z hdepth hZ hdim hf hr
  constructor
  · simpa [cloningConstant] using h.1
  · exact le_antisymm h.2 hEr

/-- The zero-difference case relies on the channel identity property.
This scalar lemma retains that hypothesis. The stronger
`CloningMatrices.theorem2_of_block_realization` derives zero actual errors
from the block data and equal zero-difference multiplicities instead. -/
theorem theorem2_zero_difference (d r D : ℕ) (q b Ef Er : ℝ)
    (hD : D = 0) (hidentity : D = 0 → Ef = 0 ∧ Er = 0) :
    Ef ≤ cloningConstant d r q * (D : ℝ) / (b + 1) ∧
      Er ≤ cloningConstant d r q * (D : ℝ) / (b + 1) := by
  obtain ⟨hf0, hr0⟩ := hidentity hD
  simp [hD, hf0, hr0]

end FreeEntropy.Theorem2
