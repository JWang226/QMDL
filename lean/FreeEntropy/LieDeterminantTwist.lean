/-
Copyright (c) 2026 Free Entropy formalization contributors.
See LICENSE and NOTICE in the repository root for license and attribution.
-/

import FreeEntropy.LieHighestUnitary
import FreeEntropy.ExteriorCanonicalHighest

/-! Scalar shifts of all diagonal Lie generators are actual determinant
twists. Their construction proves invariance of the canonical dimension
under adding a constant to every highest-weight coordinate. -/
noncomputable section
open Matrix
namespace FreeEntropy
namespace LieMatrixCasimir
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
variable {d : ℕ} {H : Type*} [Fintype H] [DecidableEq H]

def Generators.shift (R : Generators d H) (c : ℝ) : Generators d H where
  E i j := R.E i j + if i = j then c • 1 else 0
  adjoint := by
    intro i j
    by_cases hij : i = j
    · subst j; simp [R.adjoint]
    · simp [hij, Ne.symm hij, R.adjoint]
  commutator := by
    intro i j k l
    have hs : (if i = j then c • (1 : Matrix H H ℂ) else 0) * R.E k l =
        R.E k l * (if i = j then c • (1 : Matrix H H ℂ) else 0) := by
      split_ifs <;> simp [Matrix.smul_mul, Matrix.mul_smul]
    have ht : (if k = l then c • (1 : Matrix H H ℂ) else 0) * R.E i j =
        R.E i j * (if k = l then c • (1 : Matrix H H ℂ) else 0) := by
      split_ifs <;> simp [Matrix.smul_mul, Matrix.mul_smul]
    have htt : (if i = j then c • (1 : Matrix H H ℂ) else 0) *
        (if k = l then c • (1 : Matrix H H ℂ) else 0) =
        (if k = l then c • (1 : Matrix H H ℂ) else 0) *
        (if i = j then c • (1 : Matrix H H ℂ) else 0) := by
      split_ifs <;> simp
    calc
      _ = R.E i j * R.E k l - R.E k l * R.E i j := by
        rw [Matrix.add_mul, Matrix.add_mul, Matrix.mul_add, Matrix.mul_add,
          Matrix.mul_add, Matrix.mul_add, hs, ht, htt]
        abel
      _ = _ := by
        rw [R.commutator]
        by_cases hjk : j = k <;> by_cases hli : l = i
        · subst k; subst l; simp
        · subst k; simp [hli, Ne.symm hli]
        · subst l; simp [hjk, Ne.symm hjk]
        · simp [hjk, hli]


@[simp] theorem Generators.shift_offdiagonal (R : Generators d H) (c : ℝ)
    (i j : Fin d) (hij : i ≠ j) : (R.shift c).E i j = R.E i j := by simp [Generators.shift, hij]

@[simp] theorem Generators.shift_diagonal (R : Generators d H) (c : ℝ)
    (i : Fin d) : (R.shift c).E i i = R.E i i + c • 1 := by simp [Generators.shift]

theorem Generators.shift_highest_weight (R : Generators d H) (c : ℝ)
    (lam : Fin d → ℂ) (v : H → ℂ) (hw : ∀ i, R.E i i *ᵥ v = lam i • v) (i : Fin d) :
    (R.shift c).E i i *ᵥ v = (lam i + c) • v := by
  rw [R.shift_diagonal, Matrix.add_mulVec, hw, Matrix.smul_mulVec, Matrix.one_mulVec,
    add_smul]
  rfl

theorem Generators.shift_lowering_word (R : Generators d H) (c : ℝ)
    (w : List (LiePBW.Root d)) (hw : ∀ a ∈ w, a.2 < a.1) :
    LiePBW.word (R.shift c) w = LiePBW.word R w := by
  induction w with
  | nil => rfl
  | cons a w ih =>
    rw [LiePBW.word_cons, LiePBW.word_cons,
      R.shift_offdiagonal c a.1 a.2 (ne_of_gt (hw a (by simp))), ih]
    intro b hb
    exact hw b (by simp [hb])

theorem Generators.shift_loweringSpan (R : Generators d H) (c : ℝ) (v : H → ℂ) :
    LiePBW.loweringSpan (R.shift c) v = LiePBW.loweringSpan R v := by
  unfold LiePBW.loweringSpan
  congr 1
  ext x
  constructor <;> rintro ⟨w, hw, he⟩ <;> refine ⟨w, hw, ?_⟩
  · rwa [R.shift_lowering_word c w hw] at he
  · rwa [R.shift_lowering_word c w hw]

theorem Generators.shift_cyclicSpan (R : Generators d H) (c : ℝ)
    (lam : Fin d → ℂ) (v : H → ℂ) (hw : ∀ i, R.E i i *ᵥ v = lam i • v)
    (hr : ∀ i j, i < j → R.E i j *ᵥ v = 0) :
    LiePBW.cyclicSpan (R.shift c) v = LiePBW.cyclicSpan R v := by
  rw [LiePBW.cyclicSpan_eq_loweringSpan R lam v hw hr,
    LiePBW.cyclicSpan_eq_loweringSpan (R.shift c) (fun i => lam i + c) v
      (R.shift_highest_weight c lam v hw) (fun i j hij => by
        rw [R.shift_offdiagonal c i j (ne_of_lt hij)]; exact hr i j hij),
    R.shift_loweringSpan]

end LieMatrixCasimir

namespace ExteriorRepresentation
set_option backward.isDefEq.respectTransparency false
variable {d : ℕ}

theorem exists_constant_shift_unitary (mu : Fin d → ℕ) (hmu : Antitone mu) (c : ℕ) :
    ∃ W : Matrix (IrrepIndex (fun i => mu i + c)) (IrrepIndex mu) ℂ,
      Wᴴ * W = 1 ∧ W * Wᴴ = 1 ∧ ∀ i j,
        W * ((irrepGenerators mu).shift c).E i j =
          (irrepGenerators (fun i => mu i + c)).E i j * W := by
  have hshift : Antitone (fun i => mu i + c) := fun i j hij => Nat.add_le_add_right (hmu hij) c
  apply LiePBW.exists_highest_unitary ((irrepGenerators mu).shift c)
    (irrepGenerators (fun i => mu i + c)) (fun i => ((mu i + c : ℕ) : ℂ))
    (irrepHighest mu) (irrepHighest (fun i => mu i + c))
    (irrepHighest_ne_zero mu) (irrepHighest_ne_zero _)
  · intro i
    simpa only [Nat.cast_add, Complex.natCast_re, Complex.ofReal_natCast] using
      (irrepGenerators mu).shift_highest_weight c (fun i => (mu i : ℂ))
        (irrepHighest mu) (irrepHighest_weight mu hmu) i
  · exact irrepHighest_weight _ hshift
  · intro i j hij
    rw [(irrepGenerators mu).shift_offdiagonal c i j (ne_of_lt hij)]
    exact irrepHighest_raise mu i j hij
  · exact irrepHighest_raise _
  · rw [(irrepGenerators mu).shift_cyclicSpan c (fun i => (mu i : ℂ)) (irrepHighest mu)
      (irrepHighest_weight mu hmu) (irrepHighest_raise mu), irrepHighest_cyclic]
  · exact irrepHighest_cyclic _

theorem irrep_dimension_constant_shift (mu : Fin d → ℕ) (hmu : Antitone mu) (c : ℕ) :
    Module.finrank ℂ (highestSubspace (fun i => mu i + c)) =
      Module.finrank ℂ (highestSubspace mu) := by
  obtain ⟨W, hW, hW', _⟩ := exists_constant_shift_unitary mu hmu c
  have hf : Function.Bijective (Matrix.toLin' W) := by
    constructor
    · intro x y he
      have hh := congrArg (fun z => Wᴴ *ᵥ z) he
      simpa only [Matrix.toLin'_apply, Matrix.mulVec_mulVec, hW, Matrix.one_mulVec] using hh
    · intro y
      refine ⟨Wᴴ *ᵥ y, ?_⟩
      simpa only [Matrix.toLin'_apply, Matrix.mulVec_mulVec, hW', Matrix.one_mulVec]
  have h := LinearEquiv.finrank_eq (LinearEquiv.ofBijective (Matrix.toLin' W) hf)
  simpa only [Module.finrank_pi, Module.finrank_self, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, smul_eq_mul, mul_one] using h.symm

end ExteriorRepresentation
end FreeEntropy
