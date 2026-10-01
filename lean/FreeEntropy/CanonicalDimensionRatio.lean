/-
Copyright (c) 2026 Free Entropy formalization contributors.
See LICENSE and NOTICE in the repository root for license and attribution.
-/

import FreeEntropy.CanonicalDimension
import FreeEntropy.WeylFiniteSupplement

/-! The finite dimension loss for actual canonical Hilbert spaces. Signed
dominant row differences are allowed, including determinant shifts. -/
noncomputable section
open scoped BigOperators
namespace FreeEntropy.ExteriorRepresentation
open CasimirWeights
set_option backward.isDefEq.respectTransparency false
variable {d : ℕ}

def extendRow {R : Type*} [Zero R] (w : Fin d → R) (i : ℕ) : R :=
  if hi : i < d then w ⟨i, hi⟩ else 0

@[simp] theorem extendRow_apply {R : Type*} [Zero R] (w : Fin d → R) (i : Fin d) :
    extendRow w i.val = w i := by simp [extendRow]

theorem rowL1_extendRow (w : Fin d → ℝ) : Weyl.rowL1 d (extendRow w) = l1 w := by
  unfold Weyl.rowL1 l1
  rw [← Fin.sum_univ_eq_sum_range]
  simp only [extendRow_apply]

theorem canonical_dimension_extended (mu : Fin d → ℕ) (hmu : Antitone mu) (hd : 0 < d) :
    (Fintype.card (IrrepIndex mu) : ℝ) = Weyl.activeProduct d d (extendRow (fun i => (mu i : ℝ))) := by
  have hm : (fun i : Fin d => extendRow mu i.val) = mu := by funext i; simp
  have h := canonical_dimension_fullWeyl (extendRow mu) (by simpa only [hm] using hmu) hd
  rw [hm] at h
  have he : (fun i => ((extendRow mu i : ℕ) : ℝ)) = extendRow (fun i => (mu i : ℝ)) := by
    funext i
    unfold extendRow
    split_ifs <;> simp
  rw [he] at h
  simpa only [Fintype.card_fin] using h

theorem dimensionRatio_eq_extended (mu nu : Fin d → ℕ) (hmu : Antitone mu)
    (hnu : Antitone nu) (hd : 0 < d) :
    (Fintype.card (IrrepIndex mu) : ℝ) / (Fintype.card (IrrepIndex nu) : ℝ) =
      Weyl.activeProduct d d (extendRow (fun i => (mu i : ℝ))) /
        Weyl.activeProduct d d (fun i => extendRow (fun j => (mu j : ℝ)) i +
          extendRow (fun j => (nu j : ℝ) - (mu j : ℝ)) i) := by
  rw [canonical_dimension_extended mu hmu hd, canonical_dimension_extended nu hnu hd]
  congr 2
  funext i
  simp only [extendRow]
  split_ifs <;> simp

/-- Positivity and monotonicity of the genuine representation dimension ratio. -/
theorem canonical_dimensionRatio_pos_le_one (mu nu : Fin d → ℕ)
    (hmu : Antitone mu) (hnu : Antitone nu) (hd : 0 < d)
    (hinc : Antitone (fun i => (nu i : ℝ) - (mu i : ℝ))) :
    0 < (Fintype.card (IrrepIndex mu) : ℝ) / (Fintype.card (IrrepIndex nu) : ℝ) ∧
      (Fintype.card (IrrepIndex mu) : ℝ) / (Fintype.card (IrrepIndex nu) : ℝ) ≤ 1 := by
  rw [dimensionRatio_eq_extended mu nu hmu hnu hd]
  apply Weyl.weyl_ratio_pos_le_one_from_rows
  · intro i j hij hj
    have hi : i < d := hij.trans hj
    simp only [extendRow, hi, hj, dite_true]
    exact_mod_cast hmu (show (⟨i, hi⟩ : Fin d) ≤ ⟨j, hj⟩ from hij.le)
  · intro i j hij hj
    have hi : i < d := hij.trans hj
    simp only [extendRow, hi, hj, dite_true]
    exact hinc (show (⟨i, hi⟩ : Fin d) ≤ ⟨j, hj⟩ from hij.le)

/-- The dimension-loss estimate used by Theorem 2, with the dimension
formula discharged for the actual canonical source and target spaces. -/
theorem canonical_dimensionRatio_deficit (mu nu : Fin d → ℕ)
    (hmu : Antitone mu) (hnu : Antitone nu) (hd : 0 < d)
    (rank : ℕ) (b D : ℝ) (hb : 0 ≤ b)
    (hinc : Antitone (fun i => (nu i : ℝ) - (mu i : ℝ)))
    (hzero : ∀ i : Fin d, rank ≤ i.val → nu i = mu i)
    (hgap : ∀ j : Fin (d - 1), j.val < rank →
      b ≤ (mu (left j) : ℝ) - (mu (right j) : ℝ))
    (hD : l1 (fun i => (nu i : ℝ) - (mu i : ℝ)) ≤ D) :
    1 - (Fintype.card (IrrepIndex mu) : ℝ) / (Fintype.card (IrrepIndex nu) : ℝ) ≤
      (d.choose 2 : ℝ) * D / (b + 1) := by
  rw [dimensionRatio_eq_extended mu nu hmu hnu hd]
  have h := Weyl.weyl_ratio_deficit_from_rows d rank
    (extendRow (fun i => (mu i : ℝ))) (extendRow (fun i => (nu i : ℝ) - (mu i : ℝ))) b hb
  have hm : ∀ i j, i < j → j < d → extendRow (fun i => (mu i : ℝ)) j ≤
      extendRow (fun i => (mu i : ℝ)) i := by
    intro i j hij hj
    have hi : i < d := hij.trans hj
    simp only [extendRow, hi, hj, dite_true]
    exact_mod_cast hmu (show (⟨i, hi⟩ : Fin d) ≤ ⟨j, hj⟩ from hij.le)
  have hw : ∀ i j, i < j → j < d → extendRow (fun i => (nu i : ℝ) - (mu i : ℝ)) j ≤
      extendRow (fun i => (nu i : ℝ) - (mu i : ℝ)) i := by
    intro i j hij hj
    have hi : i < d := hij.trans hj
    simpa only [extendRow, hi, hj, dite_true] using
      hinc (show (⟨i, hi⟩ : Fin d) ≤ ⟨j, hj⟩ from hij.le)
  have hz : ∀ i, rank ≤ i → i < d → extendRow (fun i => (nu i : ℝ) - (mu i : ℝ)) i = 0 := by
    intro i hir hid
    simp [extendRow, hid, hzero ⟨i, hid⟩ hir]
  have hg : ∀ i, i < rank → i + 1 < d → b ≤
      extendRow (fun i => (mu i : ℝ)) i - extendRow (fun i => (mu i : ℝ)) (i + 1) := by
    intro i hir hid
    have hi : i < d := by omega
    simpa only [extendRow, hi, hid, dite_true, left, right] using
      hgap ⟨i, by omega⟩ hir
  have he := h hm hw hz hg
  rw [rowL1_extendRow] at he
  exact he.trans (div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left hD (Nat.cast_nonneg _)) (by linarith))

end FreeEntropy.ExteriorRepresentation
