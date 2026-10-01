/-
Copyright (c) 2026 Free Entropy formalization contributors.
See LICENSE and NOTICE in the repository root for license and attribution.
-/

import FreeEntropy.CloningMatrices
import FreeEntropy.WeylFiniteSupplement
import FreeEntropy.ProjectorGeometry

/-!
# Concrete cloning estimates with the Weyl loss discharged

The main theorem uses the actual row formula for the dimension ratio and
actual trace distances between CPTP outputs and targets. It does not assume
scalar error comparisons, a dimension-loss inequality, or a zero-error
channel identity. Weight-block representation facts remain explicit.
-/

noncomputable section
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator
open Matrix FreeEntropy.OrbitMemory FreeEntropy.TraceDistance
namespace FreeEntropy.CloningMatrices
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false

variable {H K ι : Type*} [Fintype H] [DecidableEq H] [Fintype K] [DecidableEq K]

/-- Only the shallow projector perturbation estimate is needed: at deeper
weights integrality makes the capped deficit one and positivity suffices. -/
theorem capped_projector_blocks {P Q : Matrix H H ℂ}
    (hP : IsStarProjection P) (hQ : IsStarProjection Q) (depth D g : ℕ)
    (hD : 1 ≤ D)
    (hshallow : depth ≤ g → ‖P - Q‖ ^ 2 ≤
      2 * (depth : ℝ) * (D : ℝ) / ((g : ℝ) + 2)) :
    (1 - min 1 (2 * (depth : ℝ) * (D : ℝ) / ((g : ℝ) + 2))) • P ≤ P * Q * P ∧
    (1 - min 1 (2 * (depth : ℝ) * (D : ℝ) / ((g : ℝ) + 2))) • Q ≤ Q * P * Q := by
  have htrivial : (0 : Matrix H H ℂ) ≤ P * Q * P ∧ (0 : Matrix H H ℂ) ≤ Q * P * Q := by
    constructor
    · have h := hQ.nonneg.posSemidef.mul_mul_conjTranspose_same P
      simpa only [show Pᴴ = P from hP.isSelfAdjoint.star_eq] using h.nonneg
    · have h := hP.nonneg.posSemidef.mul_mul_conjTranspose_same Q
      simpa only [show Qᴴ = Q from hQ.isSelfAdjoint.star_eq] using h.nonneg
  by_cases hdepth : depth ≤ g
  · by_cases hlarge : 1 ≤ 2 * (depth : ℝ) * (D : ℝ) / ((g : ℝ) + 2)
    · simpa only [min_eq_left hlarge, sub_self, zero_smul] using htrivial
    · rw [min_eq_right (le_of_not_ge hlarge)]
      exact ProjectorGeometry.projector_block_bounds hP hQ (hshallow hdepth)
  · have heq := Cloning.deficit_cap_eq_one_of_deep depth g (D : ℝ)
      (by exact_mod_cast hD) (Nat.lt_of_not_ge hdepth)
    simpa only [heq, sub_self, zero_smul] using htrivial

/-- Compression of the reverse projector estimate to the input space. -/
theorem compressed_projector_block_bound (J : Matrix K H ℂ)
    {P Q : Matrix K K ℂ} {e : ℝ}
    (hP : IsStarProjection P) (hQ : IsStarProjection Q)
    (hnorm : ‖P - Q‖ ^ 2 ≤ e) :
    (1 - e) • (Jᴴ * Q * J) ≤ Jᴴ * (Q * P * Q) * J := by
  have h := (ProjectorGeometry.projector_block_bounds hP hQ hnorm).2
  apply Matrix.le_iff.mpr
  have hcomp := (Matrix.le_iff.mp h).conjTranspose_mul_mul_same J
  simpa only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul] using hcomp

/-- Both actual cloning errors have the manuscript's constant. The Weyl
ratio and its positivity/loss estimates are derived directly from the rows.
The representation-to-block realization remains the explicit input. -/
theorem theorem2_from_rows (s : Finset ι)
    (depth m n : ι → ℕ) (pμ pν : ι → ℝ) (d r D g : ℕ)
    (b q Z : ℝ) (μ ω : ℕ → ℝ)
    (R : BlockRealization s m n pμ pν
      (fun i => min 1 (2 * (depth i : ℝ) * (D : ℝ) / ((g : ℝ) + 2)))
      (Weyl.activeProduct d d μ / Weyl.activeProduct d d (fun i => μ i + ω i)) H K)
    (hrank : 2 ≤ r) (hq : 0 ≤ q) (hq1 : q < 1)
    (hb : 0 ≤ b) (hbg : b ≤ (g : ℝ))
    (hμ : ∀ i j, i < j → j < d → μ j ≤ μ i)
    (hω : ∀ i j, i < j → j < d → ω j ≤ ω i)
    (hzero : ∀ i, r ≤ i → i < d → ω i = 0)
    (hgap : ∀ i, i < r → i + 1 < d → b ≤ μ i - μ (i + 1))
    (hD : (D : ℝ) = Weyl.rowL1 d ω)
    (hpμ : ∀ i ∈ s, 0 ≤ pμ i) (hpν : ∀ i ∈ s, 0 ≤ pν i)
    (hmn : ∀ i ∈ s, m i ≤ n i)
    (hshallow : ∀ i ∈ s, depth i ≤ g → m i = n i)
    (hzero_mult : D = 0 → ∀ i ∈ s, m i = n i)
    (hratio : ∀ i ∈ s, pν i = Z * pμ i)
    (hμ_spectral : ∀ i ∈ s, pμ i ≤ q ^ depth i)
    (hν_spectral : ∀ i ∈ s, pν i ≤ q ^ depth i)
    (hμ_mult : ∀ t, ∑ i ∈ s with depth i = t, m i ≤
      (t + r.choose 2 - 1).choose (r.choose 2 - 1))
    (hν_mult : ∀ t, ∑ i ∈ s with depth i = t, n i ≤
      (t + r.choose 2 - 1).choose (r.choose 2 - 1)) :
    traceDistance (R.forward.toFun (mixture s pμ R.Pμ)) (mixture s pν R.Pν) ≤
        Theorem2.cloningConstant d r q * (D : ℝ) / (b + 1) ∧
    traceDistance (R.reverse.toFun (mixture s pν R.Pν)) (mixture s pμ R.Pμ) ≤
        Theorem2.cloningConstant d r q * (D : ℝ) / (b + 1) := by
  obtain ⟨ha, ha1⟩ := Weyl.weyl_ratio_pos_le_one_from_rows d μ ω hμ hω
  have hdim := Weyl.weyl_ratio_deficit_from_rows d r μ ω b hb hμ hω hzero hgap
  rw [← hD] at hdim
  exact theorem2_of_block_realization s depth m n pμ pν d r D g b q _ Z R
    hrank hq hq1 hb hbg ha.le ha1 hpμ hpν hmn hshallow hzero_mult hratio
    hμ_spectral hν_spectral hμ_mult hν_mult hdim

end FreeEntropy.CloningMatrices
