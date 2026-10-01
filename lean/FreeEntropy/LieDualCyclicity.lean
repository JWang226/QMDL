/-
Copyright (c) 2026 Free Entropy formalization contributors.
See LICENSE and NOTICE in the repository root for license and attribution.
-/

import FreeEntropy.LieDual
import FreeEntropy.CyclicWeightHighest
import FreeEntropy.LieHighestUnitary

/-! The genuine contragredient of a highest cyclic star representation is
irreducible: every nonzero vector has full Lie cyclic span. -/
noncomputable section
open Matrix
namespace FreeEntropy.CartanLieCloning
open LieMatrixCasimir LiePBW
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
variable {d : ℕ} {A : Type*} [Fintype A] [DecidableEq A] [Nonempty A]

/-- No irreducibility of the contragredient is assumed. Transposing a dual
commutant and applying the original highest Schur lemma proves it. -/
theorem CyclicWeightModel.dual_cyclic_of_ne_zero (M : CyclicWeightModel d A)
    (v : A → ℂ) (hv : v ≠ 0) : cyclicSpan M.generators.dual v = ⊤ := by
  classical
  let K := cyclicSpan M.generators.dual v
  let P := projectionMatrix K
  have hK : GeneratorInvariant M.generators.dual K :=
    fun i j x hx => generator_preserves_cyclicSpan M.generators.dual v i j hx
  have hP (i j : Fin d) : Pᵀ * M.generators.E i j = M.generators.E i j * Pᵀ := by
    have h := projectionMatrix_commutes M.generators.dual hK i j
    change P * (-(M.generators.E i j)ᵀ) = (-(M.generators.E i j)ᵀ) * P at h
    have hh := congrArg Matrix.transpose h
    simp only [Matrix.transpose_mul, Matrix.transpose_neg, Matrix.transpose_transpose,
      Matrix.neg_mul, Matrix.mul_neg, neg_inj] at hh
    exact hh.symm
  obtain ⟨c, hc⟩ := commutant_scalar_of_highest M.generators (fun i => (M.row i : ℂ))
    M.highestVector M.highestVector_ne_zero M.vector_weight M.vector_raise M.vector_cyclic Pᵀ hP
  have hPc : P = c • (1 : Matrix A A ℂ) := by
    simpa only [Matrix.transpose_transpose, Matrix.transpose_smul, Matrix.transpose_one] using
      congrArg Matrix.transpose hc
  have hfix : P *ᵥ v = v := projectionMatrix_fix (self_mem_cyclicSpan M.generators.dual v)
  obtain ⟨a, ha⟩ : ∃ a, v a ≠ 0 := by
    by_contra hn
    push_neg at hn
    exact hv (funext hn)
  have hc1 : c = 1 := by
    have h := congrFun hfix a
    rw [hPc, Matrix.smul_mulVec, Matrix.one_mulVec] at h
    change c * v a = v a at h
    exact mul_right_cancel₀ ha (h.trans (one_mul _).symm)
  apply top_unique
  intro x _
  have h := projectionMatrix_mem K x
  change P *ᵥ x ∈ K at h
  simpa only [hPc, hc1, one_smul, Matrix.one_mulVec] using h

end FreeEntropy.CartanLieCloning
