/-
Copyright (c) 2026 Free Entropy formalization contributors.
See LICENSE and NOTICE in the repository root for license and attribution.
-/

import FreeEntropy.CyclicWeightHighest

/-! A nonzero subspace invariant under raising operators contains a highest
vector. Natural root depth strictly decreases under raising, so the proof
uses finite descent rather than an assumed irreducibility statement for
the subspace. -/
noncomputable section
open Matrix
open scoped BigOperators
namespace FreeEntropy.CartanLieCloning
open LieMatrixCasimir CasimirWeights
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
variable {d : ℕ} {A : Type*} [Fintype A] [DecidableEq A]

def CyclicWeightModel.basisDepth (M : CyclicWeightModel d A) (a : A) : ℕ :=
  depth (M.weightCoeff a)

theorem CyclicWeightModel.depth_eq_energy (M : CyclicWeightModel d A) (a : A) :
    (M.basisDepth a : ℝ) =
      (∑ k : Fin d, (k.val : ℝ) * M.weight a k) - ∑ k : Fin d, (k.val : ℝ) * M.row k := by
  have h := congrArg (dot (fun k : Fin d => (k.val : ℝ))) (M.weight_cone a)
  rw [dot_offset] at h
  have hr : (∑ j : Fin (d - 1), (M.weightCoeff a j : ℝ) *
      (((left j).val : ℝ) - ((right j).val : ℝ))) = -(M.basisDepth a : ℝ) := by
    simp [left, right, basisDepth, depth, Nat.cast_sum, mul_sub]
  rw [hr] at h
  dsimp [dot] at h
  simp only [Pi.sub_apply, mul_sub, Finset.sum_sub_distrib] at h
  linarith

/-- A genuine raising entry strictly decreases the natural root depth. -/
theorem CyclicWeightModel.raising_entry_depth_lt (M : CyclicWeightModel d A)
    (i j : Fin d) (hij : i < j) (a b : A) (hab : M.generators.E i j a b ≠ 0) :
    M.basisDepth a < M.basisDepth b := by
  have hs := generator_weight_shift M.generators M.weight M.diagonal i j (ne_of_lt hij) a b hab
  have he : (∑ k : Fin d, (k.val : ℝ) * M.weight a k) -
      ∑ k : Fin d, (k.val : ℝ) * M.weight b k = (i.val : ℝ) - j.val := by
    rw [← Finset.sum_sub_distrib]
    simp_rw [← mul_sub, hs]
    simp [mul_sub, Finset.sum_sub_distrib, mul_ite]
  have ha := M.depth_eq_energy a
  have hb := M.depth_eq_energy b
  have hij' : (i.val : ℝ) < j.val := by exact_mod_cast hij
  exact_mod_cast (show (M.basisDepth a : ℝ) < M.basisDepth b by linarith)

/-- Raising lowers the maximum depth in the support of any vector. -/
theorem CyclicWeightModel.raising_support_depth_lt (M : CyclicWeightModel d A)
    (i j : Fin d) (hij : i < j) (v : A → ℂ) (T : ℕ)
    (hv : ∀ b, v b ≠ 0 → M.basisDepth b ≤ T)
    (a : A) (ha : (M.generators.E i j *ᵥ v) a ≠ 0) : M.basisDepth a < T := by
  by_contra hn
  apply ha
  change ∑ b, M.generators.E i j a b * v b = 0
  apply Finset.sum_eq_zero
  intro b _
  by_cases hb : v b = 0
  · rw [hb, mul_zero]
  · have he : M.generators.E i j a b = 0 := by
      by_contra he
      have hlt := M.raising_entry_depth_lt i j hij a b he
      have hle := hv b hb
      omega
    rw [he, zero_mul]

/-- Every nonzero raising-invariant subspace contains a genuine highest
vector, constructed by finite descent in maximum support depth. -/
theorem CyclicWeightModel.exists_highest_mem_of_raising_invariant
    (M : CyclicWeightModel d A) (K : Submodule ℂ (A → ℂ)) (hK : K ≠ ⊥)
    (hraise : ∀ i j, i < j → ∀ v ∈ K, M.generators.E i j *ᵥ v ∈ K) :
    ∃ v ∈ K, v ≠ 0 ∧ ∀ i j, i < j → M.generators.E i j *ᵥ v = 0 := by
  classical
  have haux : ∀ T : ℕ, ∀ v ∈ K, v ≠ 0 → (∀ b, v b ≠ 0 → M.basisDepth b ≤ T) →
      ∃ u ∈ K, u ≠ 0 ∧ ∀ i j, i < j → M.generators.E i j *ᵥ u = 0 := by
    intro T
    induction T with
    | zero =>
      intro v hv hv0 hbound
      refine ⟨v, hv, hv0, ?_⟩
      intro i j hij
      funext a
      by_contra ha
      have hlt := M.raising_support_depth_lt i j hij v 0 hbound a ha
      omega
    | succ T ih =>
      intro v hv hv0 hbound
      by_cases hh : ∀ i j, i < j → M.generators.E i j *ᵥ v = 0
      · exact ⟨v, hv, hv0, hh⟩
      · push_neg at hh
        obtain ⟨i, j, hij, hne⟩ := hh
        apply ih (M.generators.E i j *ᵥ v) (hraise i j hij v hv) hne
        intro a ha
        exact Nat.le_of_lt_succ (M.raising_support_depth_lt i j hij v (T + 1) hbound a ha)
  obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hK
  apply haux (Finset.univ.sup M.basisDepth) v hv hv0
  intro b _
  exact Finset.le_sup (Finset.mem_univ b)

/-- A raising-invariant subspace is zero if it misses the highest line. -/
theorem CyclicWeightModel.eq_bot_of_raising_invariant [Nonempty A]
    (M : CyclicWeightModel d A) (K : Submodule ℂ (A → ℂ))
    (hraise : ∀ i j, i < j → ∀ v ∈ K, M.generators.E i j *ᵥ v ∈ K)
    (hhighest : M.highestVector ∉ K) : K = ⊥ := by
  by_contra hK
  obtain ⟨v, hv, hv0, hr⟩ := M.exists_highest_mem_of_raising_invariant K hK hraise
  obtain ⟨c, hc⟩ := M.highest_line_unique v hr
  have hc0 : c ≠ 0 := by intro hz; rw [hz, zero_smul] at hc; exact hv0 hc
  apply hhighest
  have h := K.smul_mem c⁻¹ hv
  rw [hc, smul_smul, inv_mul_cancel₀ hc0, one_smul] at h
  exact h

end FreeEntropy.CartanLieCloning
