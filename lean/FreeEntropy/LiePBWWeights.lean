/-
Copyright (c) 2026 Free Entropy formalization contributors.
See LICENSE and NOTICE in the repository root for license and attribution.
-/

import FreeEntropy.LiePBWHighest
import FreeEntropy.HighestWeightDominance

/-! Actual weights in a highest-vector cyclic space lie in the nonnegative
simple-root cone. The coefficients are derived from lowering words and
orthogonality of different joint weights. -/
noncomputable section
open Matrix
open scoped BigOperators ComplexOrder
namespace FreeEntropy.LiePBW
open LieMatrixCasimir CasimirWeights
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
set_option linter.unusedSectionVars false
variable {d : ℕ} {H : Type*} [Fintype H] [DecidableEq H]

theorem offset_add (a b : Fin (d - 1) → ℕ) : offset (a + b) = offset a + offset b := by
  ext k
  simp [offset, Nat.cast_add, add_mul, Finset.sum_add_distrib]

theorem offset_single (k : Fin (d - 1)) : offset (Pi.single k 1) = simpleRoot k := by
  ext i
  classical
  simp [offset, Pi.single_apply]

/-- Every positive root is a nonnegative integral sum of adjacent roots. -/
theorem exists_positive_root_coeff (i j : Fin d) (hji : j < i) :
    ∃ c : Fin (d - 1) → ℕ, offset c =
      (fun k => (if k = j then 1 else 0) - (if k = i then 1 else 0)) := by
  classical
  suffices ∀ m : ℕ, ∀ i j : Fin d, i.val = m → j < i →
      ∃ c : Fin (d - 1) → ℕ, offset c =
        (fun k => (if k = j then 1 else 0) - (if k = i then 1 else 0)) from
    this i.val i j rfl hji
  intro m
  induction m with
  | zero => intro i j hi hij; have : j.val < i.val := hij; omega
  | succ m ih =>
    intro i j hi hij
    let k : Fin (d - 1) := ⟨m, by have := i.isLt; omega⟩
    have hr : right k = i := Fin.ext (by simpa [right, k] using hi.symm)
    have hj : j ≤ left k := by change j.val ≤ m; have : j.val < i.val := hij; omega
    by_cases he : j = left k
    · refine ⟨Pi.single k 1, ?_⟩
      rw [offset_single]
      ext t
      simp [simpleRoot, hr, he]
    · obtain ⟨c, hc⟩ := ih (left k) j rfl (lt_of_le_of_ne hj he)
      refine ⟨c + Pi.single k 1, ?_⟩
      rw [offset_add, hc, offset_single]
      ext t
      simp only [Pi.add_apply, simpleRoot, hr]
      ring

theorem raising_weight_real (R : Generators d H) (lam : Fin d → ℝ)
    (v : H → ℂ) (hv : ∀ k, R.E k k *ᵥ v = lam k • v) (i j k : Fin d) :
    R.E k k *ᵥ (R.E i j *ᵥ v) =
      (lam k + (if k = i then 1 else 0) - (if k = j then 1 else 0)) • (R.E i j *ᵥ v) := by
  have h := R.raising_weight (fun k => (lam k : ℂ)) v (fun k => by simpa using hv k) i j k
  convert h using 1
  ext b
  simp only [Pi.smul_apply, Complex.real_smul, Complex.ofReal_add, Complex.ofReal_sub,
    apply_ite, Complex.ofReal_one, Complex.ofReal_zero, smul_eq_mul]

/-- A lowering word has a weight obtained by subtracting actual nonnegative
simple-root coefficients from the highest weight. -/
theorem lowering_word_weight (R : Generators d H) (lam : Fin d → ℝ) (v : H → ℂ)
    (hv : ∀ k, R.E k k *ᵥ v = lam k • v) (w : List (Root d))
    (hw : ∀ a ∈ w, a.2 < a.1) :
    ∃ c : Fin (d - 1) → ℕ, ∀ k,
      R.E k k *ᵥ (word R w *ᵥ v) = (lam k - offset c k) • (word R w *ᵥ v) := by
  induction w with
  | nil => refine ⟨0, ?_⟩; intro k; simpa [offset] using hv k
  | cons a w ih =>
    obtain ⟨c, hc⟩ := ih (fun b hb => hw b (List.mem_cons_of_mem a hb))
    obtain ⟨b, hb⟩ := exists_positive_root_coeff a.1 a.2 (hw a List.mem_cons_self)
    refine ⟨c + b, ?_⟩
    intro k
    simp only [word_cons, ← Matrix.mulVec_mulVec]
    rw [raising_weight_real R (fun k => lam k - offset c k) (word R w *ᵥ v) hc]
    congr 1
    have hbk := congrFun hb k
    simp only [offset_add, Pi.add_apply]
    linarith

theorem exists_nonorthogonal_lowering_word (R : Generators d H) (v u : H → ℂ)
    (hu : u ∈ loweringSpan R v) (hu0 : u ≠ 0) :
    ∃ w : List (Root d), (∀ a ∈ w, a.2 < a.1) ∧ star u ⬝ᵥ (word R w *ᵥ v) ≠ 0 := by
  by_contra! hn
  have hall (x : H → ℂ) (hx : x ∈ loweringSpan R v) : star u ⬝ᵥ x = 0 := by
    induction hx using Submodule.span_induction with
    | mem x hx => obtain ⟨w, hw, rfl⟩ := hx; exact hn w hw
    | zero => simp
    | add x y hx hy hx' hy' => simp [dotProduct_add, hx', hy']
    | smul c x hx hx' => simp [dotProduct_smul, hx']
  exact hu0 (dotProduct_star_self_eq_zero.mp (hall u hu))

/-- Joint eigenvectors with nonzero inner product have the same real weight. -/
theorem weights_equal_of_nonorthogonal (R : Generators d H) (mu nu : Fin d → ℝ)
    (u v : H → ℂ) (hu : ∀ k, R.E k k *ᵥ u = mu k • u)
    (hv : ∀ k, R.E k k *ᵥ v = nu k • v) (hn : star u ⬝ᵥ v ≠ 0) : mu = nu := by
  funext k
  have hs : star u ᵥ* R.E k k = star (R.E k k *ᵥ u) := by
    calc
      _ = star u ᵥ* (R.E k k)ᴴ := by rw [R.adjoint]
      _ = _ := by rw [Matrix.vecMul_conjTranspose, star_star]
  have he : (mu k : ℂ) * (star u ⬝ᵥ v) = (nu k : ℂ) * (star u ⬝ᵥ v) := by
    calc
      _ = star (R.E k k *ᵥ u) ⬝ᵥ v := by simp [hu, star_smul, smul_dotProduct]
      _ = star u ⬝ᵥ (R.E k k *ᵥ v) := by rw [dotProduct_mulVec, hs]
      _ = _ := by simp [hv, dotProduct_smul]
  exact Complex.ofReal_injective (mul_right_cancel₀ hn he)

/-- The root-cone condition for every actual weight vector follows from PBW.
No root-cone assignment is assumed. -/
theorem weight_in_root_cone (R : Generators d H) (lam mu : Fin d → ℝ)
    (v u : H → ℂ) (hweight : ∀ k, R.E k k *ᵥ v = lam k • v)
    (hraise : ∀ i j, i < j → R.E i j *ᵥ v = 0)
    (hu : u ∈ cyclicSpan R v) (hu0 : u ≠ 0)
    (huw : ∀ k, R.E k k *ᵥ u = mu k • u) :
    ∃ c : Fin (d - 1) → ℕ, lam - mu = offset c := by
  have hul : u ∈ loweringSpan R v := by
    rwa [← cyclicSpan_eq_loweringSpan R (fun k => (lam k : ℂ)) v
      (fun k => by simpa using hweight k) hraise]
  obtain ⟨w, hw, hn⟩ := exists_nonorthogonal_lowering_word R v u hul hu0
  obtain ⟨c, hc⟩ := lowering_word_weight R lam v hweight w hw
  have he := weights_equal_of_nonorthogonal R mu (fun k => lam k - offset c k)
    u (word R w *ᵥ v) huw hc hn
  refine ⟨c, ?_⟩
  ext k
  have hk := congrFun he k
  simp only [Pi.sub_apply]
  linarith

end FreeEntropy.LiePBW
