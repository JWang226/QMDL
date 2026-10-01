/-
Copyright (c) 2026 Free Entropy formalization contributors.
See LICENSE and NOTICE in the repository root for license and attribution.
-/

import FreeEntropy.ExteriorTensor

/-! Literal columns of an arbitrary dominant natural highest weight. -/
noncomputable section
open scoped BigOperators
namespace FreeEntropy.ExteriorRepresentation

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

variable {d : ℕ} (mu : Fin d → ℕ)

abbrev Column := Fin (∑ i, mu i)

/-- Column heights are obtained by counting cells of the actual Young diagram.
Trailing zero-height columns are harmless trivial exterior factors. -/
def columnHeight (c : Column mu) : ℕ :=
  (Finset.univ.filter (fun i : Fin d => c.val < mu i)).card

theorem columnHeight_le (c : Column mu) : columnHeight mu c ≤ d := by
  exact (Finset.card_filter_le _ _).trans_eq (Fintype.card_fin d)

theorem columnHeight_mem (hmu : Antitone mu) (c : Column mu) (i : Fin d) :
    i.val < columnHeight mu c ↔ c.val < mu i := by
  classical
  let s := Finset.univ.filter (fun j : Fin d => c.val < mu j)
  constructor
  · intro hi
    by_contra hn
    have hs : s.image Fin.val ⊆ Finset.range i.val := by
      intro a ha
      obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp ha
      apply Finset.mem_range.mpr
      have hmem : c.val < mu j := (Finset.mem_filter.mp hj).2
      by_contra hji
      have hle : i ≤ j := Nat.le_of_not_gt hji
      have hanti := hmu hle
      omega
    have hc := Finset.card_le_card hs
    rw [Finset.card_image_of_injective _ Fin.val_injective, Finset.card_range] at hc
    exact (Nat.not_lt_of_ge hc) hi
  · intro hi
    let f : Fin (i.val + 1) → {j // j ∈ s} := fun t =>
      ⟨⟨t.val, by omega⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _,
        lt_of_lt_of_le hi (hmu (show (⟨t.val, by omega⟩ : Fin d) ≤ i by exact Nat.le_of_lt_succ t.isLt))⟩⟩
    have hf : Function.Injective f := by
      intro a b he
      exact Fin.ext (congrArg (fun j => j.val.val) he)
    have hc := Fintype.card_le_of_injective f hf
    simp only [Fintype.card_fin, Fintype.card_coe] at hc
    exact Nat.lt_of_succ_le hc

/-- The highest tensor basis vector has exactly the prescribed dominant row. -/
theorem tensorFirst_weight (hmu : Antitone mu) :
    tensorWeight (columnHeight mu) (tensorFirst (columnHeight mu) (columnHeight_le mu)) = mu := by
  classical
  funext i
  have hsum : tensorWeight (columnHeight mu)
      (tensorFirst (columnHeight mu) (columnHeight_le mu)) i =
      (Finset.univ.filter (fun c : Column mu => c.val < mu i)).card := by
    simp only [tensorWeight, tensorFirst, weight, mem_first_iff, columnHeight_mem mu hmu]
    simp
  rw [hsum]
  have hle : mu i ≤ ∑ j, mu j :=
    Finset.single_le_sum (fun j _ => Nat.zero_le _) (Finset.mem_univ i)
  calc
    _ = (Finset.univ : Finset (Fin (mu i))).card := by
      apply Finset.card_bij (fun c hc => (⟨c.val, (Finset.mem_filter.mp hc).2⟩ : Fin (mu i)))
      · intro c hc
        exact Finset.mem_univ _
      · intro a ha b hb he
        exact Fin.ext (congrArg (fun t : Fin (mu i) => t.val) he)
      · intro b hb
        refine ⟨⟨b.val, lt_of_lt_of_le b.isLt hle⟩, ?_, ?_⟩
        · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, b.isLt⟩
        · rfl
    _ = _ := Finset.card_fin _

/-- Highest-weight multiplicity one in the constructed exterior tensor. -/
theorem prescribed_weight_unique (hmu : Antitone mu)
    (x : TensorIndex (d := d) (columnHeight mu)) :
    tensorWeight (columnHeight mu) x = mu ↔
      x = tensorFirst (columnHeight mu) (columnHeight_le mu) := by
  simpa only [tensorFirst_weight mu hmu] using
    tensorWeight_eq_highest_iff (columnHeight mu) (columnHeight_le mu) x

/-- Every actual tensor basis weight is dominated by the prescribed row. -/
theorem weight_prefix_dominated (hmu : Antitone mu)
    (x : TensorIndex (d := d) (columnHeight mu)) (t : ℕ) :
    (∑ i : Fin d with i.val < t, tensorWeight (columnHeight mu) x i) ≤
      ∑ i : Fin d with i.val < t, mu i := by
  simpa only [tensorFirst_weight mu hmu] using
    tensor_prefix_le_highest (columnHeight mu) (columnHeight_le mu) x t

/-- The representation's actual weights all have the prescribed total degree. -/
theorem weight_total_eq (hmu : Antitone mu)
    (x : TensorIndex (d := d) (columnHeight mu)) :
    (∑ i : Fin d, tensorWeight (columnHeight mu) x i) = ∑ i, mu i := by
  have h := tensor_sum_weight (columnHeight mu)
    (tensorFirst (columnHeight mu) (columnHeight_le mu))
  rw [tensorFirst_weight mu hmu] at h
  exact (tensor_sum_weight (columnHeight mu) x).trans h.symm

/-- In the tensor product of two actual exterior ambient spaces, only the
pair of highest vectors has the sum of the highest weights. -/
theorem pair_weight_unique (nu : Fin d → ℕ) (hmu : Antitone mu) (hnu : Antitone nu)
    (x : TensorIndex (d := d) (columnHeight mu))
    (y : TensorIndex (d := d) (columnHeight nu))
    (hw : tensorWeight (columnHeight mu) x + tensorWeight (columnHeight nu) y = mu + nu) :
    x = tensorFirst (columnHeight mu) (columnHeight_le mu) ∧
      y = tensorFirst (columnHeight nu) (columnHeight_le nu) := by
  have he := congrArg (fun w : Fin d → ℕ => ∑ i, i.val * w i) hw
  simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib,
    ← tensorEnergy_eq_weight_sum] at he
  have hxm := tensorEnergy_highest_le (columnHeight mu) (columnHeight_le mu) x
  have hyn := tensorEnergy_highest_le (columnHeight nu) (columnHeight_le nu) y
  have hem : tensorEnergy (columnHeight mu)
      (tensorFirst (columnHeight mu) (columnHeight_le mu)) = ∑ i, i.val * mu i := by
    rw [tensorEnergy_eq_weight_sum, tensorFirst_weight mu hmu]
  have hen : tensorEnergy (columnHeight nu)
      (tensorFirst (columnHeight nu) (columnHeight_le nu)) = ∑ i, i.val * nu i := by
    rw [tensorEnergy_eq_weight_sum, tensorFirst_weight nu hnu]
  constructor
  · apply (tensorEnergy_eq_highest_iff (columnHeight mu) (columnHeight_le mu) x).mp
    omega
  · apply (tensorEnergy_eq_highest_iff (columnHeight nu) (columnHeight_le nu) y).mp
    omega

end FreeEntropy.ExteriorRepresentation
