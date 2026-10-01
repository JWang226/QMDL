/-
Copyright (c) 2026 Free Entropy formalization contributors.
See LICENSE and NOTICE in the repository root for license and attribution.
-/

import FreeEntropy.Statements
import Mathlib.Data.Finset.Lattice.Fold

/-!
# Explicit spectrum constants for the converse

For a fixed spectrum the paper's `q_x` and `γ_x` are defined and proved to
satisfy `0 ≤ q_x < 1` and `γ_x > 0`. The resulting eigenvalue-gap estimate
keeps the representation-theoretic bounds on the top two eigenvalues as
explicit hypotheses; no spectral theorem about irreducible states is assumed
as an axiom.
-/

noncomputable section
open scoped BigOperators

namespace FreeEntropy.FixedSpectrum

variable {d r : ℕ}

/-- An adjacent eigenvalue ratio, with zero at the last index. This lets the
maximum have a nonempty index set even in rank one. -/
def adjacentRatio (s : FixedSpectrum d r) (i : ℕ) : ℝ :=
  if i + 1 < r then s.eigenvalue (i + 1) / s.eigenvalue i else 0

/-- The paper's `q_x`: maximum adjacent positive-eigenvalue ratio, with
the specified zero convention in rank one. -/
def qx (s : FixedSpectrum d r) : ℝ :=
  (Finset.range r).sup' (Finset.nonempty_range_iff.mpr s.rank_pos.ne') s.adjacentRatio

theorem adjacentRatio_nonneg (s : FixedSpectrum d r) (i : ℕ) :
    0 ≤ s.adjacentRatio i := by
  unfold adjacentRatio
  split_ifs with hi
  · exact div_nonneg (s.positive (i + 1) hi).le (s.positive i (by omega)).le
  · exact le_rfl

theorem adjacentRatio_lt_one (s : FixedSpectrum d r) (i : ℕ) :
    s.adjacentRatio i < 1 := by
  unfold adjacentRatio
  split_ifs with hi
  · apply (div_lt_one (s.positive i (by omega))).mpr
    exact s.decreasing i (i + 1) (by omega) hi
  · norm_num

theorem qx_nonneg (s : FixedSpectrum d r) : 0 ≤ s.qx := by
  have hmem : 0 ∈ Finset.range r := Finset.mem_range.mpr s.rank_pos
  exact (s.adjacentRatio_nonneg 0).trans (Finset.le_sup' s.adjacentRatio hmem)

theorem qx_lt_one (s : FixedSpectrum d r) : s.qx < 1 := by
  exact (Finset.sup'_lt_iff _).mpr (fun i _ => s.adjacentRatio_lt_one i)

/-- Every adjacent ratio occurring in the paper is bounded by `q_x`. -/
theorem adjacent_ratio_le_qx (s : FixedSpectrum d r) (i : ℕ) (hi : i + 1 < r) :
    s.eigenvalue (i + 1) / s.eigenvalue i ≤ s.qx := by
  have hmem : i ∈ Finset.range r := Finset.mem_range.mpr (by omega)
  have h : s.adjacentRatio i ≤ s.qx := Finset.le_sup' s.adjacentRatio hmem
  simpa only [adjacentRatio, hi, ↓reduceIte] using h

/-- This universal property confirms that adding the zero convention does
not alter the maximum of the positive adjacent ratios. -/
theorem qx_le (s : FixedSpectrum d r) {q : ℝ} (hq : 0 ≤ q)
    (hbound : ∀ i, i + 1 < r → s.eigenvalue (i + 1) / s.eigenvalue i ≤ q) :
    s.qx ≤ q := by
  apply Finset.sup'_le
  intro i _
  unfold adjacentRatio
  split_ifs with hi
  · exact hbound i hi
  · exact hq

@[simp] theorem qx_rank_one (s : FixedSpectrum d 1) : s.qx = 0 := by
  simp [qx, adjacentRatio]

/-- The product lower bound for the largest representation-state eigenvalue,
indexed by positive roots among the nonzero eigenvalues. -/
def spectralProduct (s : FixedSpectrum d r) : ℝ :=
  ∏ p ∈ Weyl.activeRoots r r, (1 - s.eigenvalue p.2 / s.eigenvalue p.1)

theorem spectralProduct_pos (s : FixedSpectrum d r) : 0 < s.spectralProduct := by
  apply Finset.prod_pos
  intro p hp
  obtain ⟨hi, hij, hj⟩ := Weyl.mem_activeRoots.mp hp
  apply sub_pos.mpr
  exact (div_lt_one (s.positive p.1 hi)).mpr (s.decreasing p.1 p.2 hij hj)

/-- Exactly the uniform spectral-gap constant `γ_x` in the manuscript. -/
def gammaX (s : FixedSpectrum d r) : ℝ := (1 - s.qx) * s.spectralProduct

theorem gammaX_pos (s : FixedSpectrum d r) : 0 < s.gammaX := by
  exact mul_pos (sub_pos.mpr s.qx_lt_one) s.spectralProduct_pos

@[simp] theorem spectralProduct_rank_one (s : FixedSpectrum d 1) :
    s.spectralProduct = 1 := by
  simp [spectralProduct, Weyl.activeRoots]

@[simp] theorem gammaX_rank_one (s : FixedSpectrum d 1) : s.gammaX = 1 := by
  simp [gammaX]

/-- The scalar conclusion of the uniform spectral-gap lemma. Establishing
the two eigenvalue bounds for actual representation states remains external. -/
theorem gammaX_le_eigenvalue_gap (s : FixedSpectrum d r) {p₀ p₁ : ℝ}
    (htop : s.spectralProduct ≤ p₀) (hnext : p₁ ≤ s.qx * p₀) :
    s.gammaX ≤ p₀ - p₁ := by
  have h := mul_le_mul_of_nonneg_left htop (sub_pos.mpr s.qx_lt_one).le
  unfold gammaX
  nlinarith

theorem eigenvalue_gap_pos (s : FixedSpectrum d r) {p₀ p₁ : ℝ}
    (htop : s.spectralProduct ≤ p₀) (hnext : p₁ ≤ s.qx * p₀) :
    0 < p₀ - p₁ := s.gammaX_pos.trans_le (s.gammaX_le_eigenvalue_gap htop hnext)

/-- Replace a representation-dependent gap by the fixed spectrum constant
in the finite memory lower bound. -/
theorem memory_bound_with_gammaX (s : FixedSpectrum d r)
    {dim memory error gap : ℝ} (hdim : 0 ≤ dim) (herror : 0 ≤ error)
    (hgap : s.gammaX ≤ gap)
    (hbound : dim * (1 - error / gap) ≤ memory) :
    dim * (1 - error / s.gammaX) ≤ memory := by
  have hdiv := div_le_div_of_nonneg_left herror s.gammaX_pos hgap
  have hcoef : 1 - error / s.gammaX ≤ 1 - error / gap := by linarith
  exact (mul_le_mul_of_nonneg_left hcoef hdim).trans hbound

end FreeEntropy.FixedSpectrum

namespace FreeEntropy

open Filter
open scoped Topology

/-- Theorem 1's converse with the paper's exact fixed positive gap, rather
than an arbitrary gap parameter. The finite memory inequality remains a
visible quantum input. -/
theorem theorem1_converse_with_spectrum_gap
    {d r : ℕ} (s : FixedSpectrum d r) (memory target : ℕ → ℕ)
    (δ e : ℕ → ℝ)
    (hdim : ∀ᶠ n in atTop,
      (target n : ℝ) = Weyl.activeProduct d r (s.targetRow n))
    (htarget : ∀ n, 0 < target n)
    (hδ : Tendsto δ atTop (𝓝 0)) (he : Asymptotics.IsBigO atTop e Weyl.errorScale)
    (hbound : ∀ᶠ n in atTop,
      (target n : ℝ) * (1 - (δ n + e n) / s.gammaX) ≤ memory n) :
    (0 : EReal) ≤ liminf
      (fun n => ((Real.logb 2 (memory n) - Weyl.qmdl d r s.eigenvalue n : ℝ) : EReal)) atTop :=
  theorem1_converse_of_quantum_estimates s memory target δ e s.gammaX
    hdim htarget s.gammaX_pos hδ he hbound

end FreeEntropy
