/-
Copyright (c) 2026 Free Entropy formalization contributors.
See LICENSE and NOTICE in the repository root for license and attribution.
-/

import FreeEntropy.TensorWeightBasis
import FreeEntropy.LiePBWWeights

/-! Every finite unitary matrix Lie action has a highest vector. A joint
orthonormal eigenbasis and finite energy minimization construct it. -/
noncomputable section
open Matrix
open scoped BigOperators ComplexInnerProductSpace
namespace FreeEntropy.LieMatrixCasimir
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
variable {d : ℕ} {A : Type*} [Fintype A] [DecidableEq A]

/-- The simultaneous eigenvalues of the self-adjoint diagonal generators
are real; this follows from the actual Hermitian inner-product identity. -/
theorem Generators.exists_real_jointBasis (R : Generators d A) :
    ∃ b : OrthonormalBasis A ℂ (EuclideanSpace ℂ A), ∃ χ : A → Fin d → ℝ,
      ∀ a j, R.E j j *ᵥ (b a).ofLp = χ a j • (b a).ofLp := by
  obtain ⟨b, χ, hχ⟩ := R.exists_jointBasis
  have him (a : A) (j : Fin d) : (χ a j).im = 0 := by
    have hT := Matrix.isHermitian_iff_isSymmetric.mp (R.adjoint j j)
    have h := hT.im_inner_self_apply (b a)
    have he : Matrix.toEuclideanLin (R.E j j) (b a) = χ a j • b a := by
      apply WithLp.ofLp_injective 2
      exact hχ a j
    rw [he, inner_smul_right, b.inner_eq_one, mul_one] at h
    exact h
  refine ⟨b, fun a j => (χ a j).re, ?_⟩
  intro a j
  have hc : ((χ a j).re : ℂ) = χ a j := by
    apply Complex.ext <;> simp [him]
  funext k
  have he := congrFun (hχ a j) k
  change _ = χ a j * (b a).ofLp k at he
  rw [← hc] at he
  simpa only [Pi.smul_apply, Complex.real_smul, smul_eq_mul] using he

/-- A highest vector is obtained by minimizing the finite energy
`sum j * weight_j` among a constructed joint eigenbasis. -/
theorem Generators.exists_highest [Nonempty A] (R : Generators d A) :
    ∃ lam : Fin d → ℝ, ∃ v : A → ℂ, v ≠ 0 ∧ Antitone lam ∧
      (∀ j, R.E j j *ᵥ v = lam j • v) ∧
      (∀ i j, i < j → R.E i j *ᵥ v = 0) := by
  classical
  obtain ⟨b, χ, hb⟩ := R.exists_real_jointBasis
  let energy (a : A) := ∑ k : Fin d, (k.val : ℝ) * χ a k
  obtain ⟨a, _, hmin⟩ := Finset.exists_min_image Finset.univ energy Finset.univ_nonempty
  let v := (b a).ofLp
  have hv : v ≠ 0 := by
    intro h
    have he : b a = 0 := WithLp.ofLp_injective 2 h
    have hn := b.norm_eq_one a
    rw [he, norm_zero] at hn
    exact zero_ne_one hn
  have hraise (i j : Fin d) (hij : i < j) : R.E i j *ᵥ v = 0 := by
    by_contra hne
    let y := R.E i j *ᵥ v
    have hex : ∃ c : A, star (b c).ofLp ⬝ᵥ y ≠ 0 := by
      by_contra hn
      push_neg at hn
      have hy : b.repr (WithLp.toLp 2 y) = 0 := by
        apply WithLp.ofLp_injective 2
        funext c
        simpa only [OrthonormalBasis.repr_apply_apply,
          EuclideanSpace.inner_eq_star_dotProduct, WithLp.ofLp_toLp, WithLp.ofLp_zero,
          Pi.zero_apply, dotProduct_comm] using hn c
      have hy0 : WithLp.toLp 2 y = (0 : EuclideanSpace ℂ A) :=
        b.repr.injective (by simpa using hy)
      exact hne (congrArg WithLp.ofLp hy0)
    obtain ⟨c, hc⟩ := hex
    let mu : Fin d → ℝ := fun k => χ a k + (if k = i then 1 else 0) - (if k = j then 1 else 0)
    have hy (k : Fin d) : R.E k k *ᵥ y = mu k • y := by
      have h := R.raising_weight (fun k => (χ a k : ℂ)) v
        (fun k => by simpa using hb a k) i j k
      have hs : (mu k : ℂ) = (χ a k : ℂ) +
          (if k = i then 1 else 0) - (if k = j then 1 else 0) := by
        simp only [mu, Complex.ofReal_sub, Complex.ofReal_add, apply_ite,
          Complex.ofReal_one, Complex.ofReal_zero]
        split_ifs <;> rfl
      funext q
      have he := congrFun h q
      change _ = ((χ a k : ℂ) + (if k = i then 1 else 0) -
        (if k = j then 1 else 0)) * y q at he
      rw [← hs] at he
      simpa only [Pi.smul_apply, Complex.real_smul, smul_eq_mul] using he
    have he := LiePBW.weights_equal_of_nonorthogonal R (χ c) mu (b c).ofLp y
      (hb c) hy hc
    have henergy : energy c = energy a + (i.val : ℝ) - (j.val : ℝ) := by
      simp only [energy, he, mu, mul_sub, mul_add, Finset.sum_sub_distrib,
        Finset.sum_add_distrib, mul_ite, mul_one, mul_zero]
      simp
    have hm := hmin c (Finset.mem_univ c)
    have hij' : (i.val : ℝ) < (j.val : ℝ) := by exact_mod_cast hij
    linarith
  exact ⟨χ a, v, hv, R.highest_weight_dominant (χ a) v hv (hb a) hraise, hb a, hraise⟩

end FreeEntropy.LieMatrixCasimir
