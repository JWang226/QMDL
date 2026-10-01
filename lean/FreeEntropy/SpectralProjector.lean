/-
Copyright (c) 2026 Free Entropy formalization contributors.
See LICENSE and NOTICE in the repository root for license and attribution.
-/

import FreeEntropy.OrbitMemory
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Algebra.Star.StarProjection

/-!
# Concrete eigenprojectors and spectral upper bounds

The projector is constructed from the spectral theorem's actual eigenvector
unitary. Positivity, trace one, peak overlap, and the operator upper bound
are proved from the corresponding scalar eigenvalue inequalities.
-/

noncomputable section
open Matrix
open scoped MatrixOrder ComplexOrder BigOperators

namespace FreeEntropy.SpectralProjector

set_option backward.isDefEq.respectTransparency false

variable {H : Type*} [Fintype H] [DecidableEq H]

def coordinateProjection (k : H) : Matrix H H ℂ :=
  diagonal (fun i => if i = k then 1 else 0)

omit [Fintype H] in
theorem coordinateProjection_pos (k : H) : (coordinateProjection k).PosSemidef := by
  apply Matrix.PosSemidef.diagonal
  intro i
  change (0 : ℂ) ≤ if i = k then 1 else 0
  split_ifs <;> simp

@[simp] theorem coordinateProjection_trace (k : H) : (coordinateProjection k).trace = 1 := by
  simp [coordinateProjection]

theorem coordinateProjection_isStarProjection (k : H) :
    IsStarProjection (coordinateProjection k) := by
  rw [isStarProjection_iff']
  constructor
  · unfold coordinateProjection
    rw [Matrix.diagonal_mul_diagonal]
    congr 1
    funext i
    split_ifs <;> simp
  · exact (coordinateProjection_pos k).isHermitian

/-- The rank-one projector onto the selected spectral-basis eigenvector. -/
def eigenProjection {τ : Matrix H H ℂ} (hτ : τ.IsHermitian) (k : H) : Matrix H H ℂ :=
  Unitary.conjStarAlgAut ℂ _ hτ.eigenvectorUnitary (coordinateProjection k)

theorem eigenProjection_isStarProjection {τ : Matrix H H ℂ}
    (hτ : τ.IsHermitian) (k : H) : IsStarProjection (eigenProjection hτ k) :=
  (coordinateProjection_isStarProjection k).map
    (Unitary.conjStarAlgAut ℂ _ hτ.eigenvectorUnitary)

theorem eigenProjection_pos {τ : Matrix H H ℂ} (hτ : τ.IsHermitian) (k : H) :
    (eigenProjection hτ k).PosSemidef := by
  have h := (coordinateProjection_pos k).mul_mul_conjTranspose_same hτ.eigenvectorUnitary.val
  simpa [eigenProjection, Unitary.conjStarAlgAut_apply, Matrix.star_eq_conjTranspose] using h

@[simp] theorem eigenProjection_trace {τ : Matrix H H ℂ} (hτ : τ.IsHermitian) (k : H) :
    (eigenProjection hτ k).trace = 1 := by
  rw [eigenProjection, Unitary.conjStarAlgAut_apply, Matrix.trace_mul_cycle,
    Unitary.coe_star_mul_self, Matrix.one_mul, coordinateProjection_trace]

theorem eigenProjection_mul {τ : Matrix H H ℂ} (hτ : τ.IsHermitian) (k : H) :
    eigenProjection hτ k * τ = (hτ.eigenvalues k : ℂ) • eigenProjection hτ k := by
  have hd : coordinateProjection k * diagonal (RCLike.ofReal ∘ hτ.eigenvalues) =
      (hτ.eigenvalues k : ℂ) • coordinateProjection k := by
    unfold coordinateProjection
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_smul]
    congr 1
    funext i
    by_cases hi : i = k <;> simp [hi]
  unfold eigenProjection
  conv_lhs => rhs; rw [hτ.spectral_theorem]
  rw [← map_mul, hd, map_smul]

/-- The exact peak overlap used in the orbit memory argument. -/
theorem eigenProjection_peak {τ : Matrix H H ℂ} (hτ : τ.IsHermitian) (k : H) :
    OrbitMemory.tr (eigenProjection hτ k * τ) = hτ.eigenvalues k := by
  rw [eigenProjection_mul, OrbitMemory.tr, Matrix.trace_smul, eigenProjection_trace]
  simp

/-- Scalar eigenvalue bounds give the operator inequality required in the
converse. No positivity, rank, or testing assumption about a free projector
is supplied: the projector is the explicit one above. -/
theorem spectral_upper_bound {τ : Matrix H H ℂ} (hτ : τ.IsHermitian) (k : H)
    {p₀ p₁ : ℝ} (hpeak : hτ.eigenvalues k = p₀)
    (hother : ∀ i, i ≠ k → hτ.eigenvalues i ≤ p₁) :
    τ ≤ p₁ • (1 : Matrix H H ℂ) + (p₀ - p₁) • eigenProjection hτ k := by
  let cap : H → ℝ := fun i => if i = k then p₀ else p₁
  have hcap (i : H) : hτ.eigenvalues i ≤ cap i := by
    by_cases hi : i = k
    · simp [cap, hi, hpeak]
    · simpa [cap, hi] using hother i hi
  have hD : (diagonal (fun i => (cap i : ℂ)) -
      diagonal (fun i => (hτ.eigenvalues i : ℂ))).PosSemidef := by
    rw [Matrix.diagonal_sub]
    apply Matrix.PosSemidef.diagonal
    intro i
    change (0 : ℂ) ≤ (cap i : ℂ) - (hτ.eigenvalues i : ℂ)
    rw [← Complex.ofReal_sub]
    exact Complex.zero_le_real.mpr (sub_nonneg.mpr (hcap i))
  have hcapdiag : diagonal (fun i => (cap i : ℂ)) =
      p₁ • (1 : Matrix H H ℂ) + (p₀ - p₁) • coordinateProjection k := by
    ext i j
    by_cases hij : i = j
    · subst j
      by_cases hik : i = k <;>
        simp [cap, coordinateProjection, Matrix.smul_apply, hik, Complex.real_smul,
          Complex.ofReal_sub]
    · simp [coordinateProjection, Matrix.smul_apply, hij]
  have hdecomp : hτ.eigenvectorUnitary.val *
      diagonal (fun i => (hτ.eigenvalues i : ℂ)) * hτ.eigenvectorUnitary.valᴴ = τ := by
    simpa [Unitary.conjStarAlgAut_apply, Matrix.star_eq_conjTranspose, Function.comp_def]
      using hτ.spectral_theorem.symm
  have hconj := hD.mul_mul_conjTranspose_same hτ.eigenvectorUnitary.val
  have hUU := Unitary.mul_star_self_of_mem hτ.eigenvectorUnitary.prop
  apply Matrix.le_iff.mpr
  rw [Matrix.mul_sub, Matrix.sub_mul, hdecomp, hcapdiag] at hconj
  simpa only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul,
    Matrix.mul_one, ← Matrix.star_eq_conjTranspose, hUU,
    eigenProjection, Unitary.conjStarAlgAut_apply] using hconj

end FreeEntropy.SpectralProjector
