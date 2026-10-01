/-
Copyright (c) 2026 Free Entropy formalization contributors.
See LICENSE and NOTICE in the repository root for license and attribution.
-/

import FreeEntropy.ExteriorDominant
import Mathlib.Logic.Equiv.Basic

/-! Adding dominant rows concatenates their actual exterior column factors. -/
noncomputable section
open scoped BigOperators
namespace FreeEntropy.ExteriorRepresentation

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

variable {d : ℕ} (mu : Fin d → ℕ)

def heightTail (t : ℕ) : ℕ :=
  (Finset.univ.filter (fun c : Column mu => t < columnHeight mu c)).card

def rowAt (t : ℕ) : ℕ := if ht : t < d then mu ⟨t, ht⟩ else 0

theorem heightTail_eq (hmu : Antitone mu) (t : ℕ) : heightTail mu t = rowAt mu t := by
  classical
  by_cases ht : t < d
  · simp only [heightTail, rowAt, dif_pos ht]
    have hf : (Finset.univ.filter (fun c : Column mu => t < columnHeight mu c)) =
        Finset.univ.filter (fun c => c.val < mu ⟨t, ht⟩) := by
      ext c
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact columnHeight_mem mu hmu c ⟨t, ht⟩
    rw [hf]
    have hle : mu ⟨t, ht⟩ ≤ ∑ j, mu j :=
      Finset.single_le_sum (fun j _ => Nat.zero_le _) (Finset.mem_univ _)
    calc
      _ = (Finset.univ : Finset (Fin (mu ⟨t, ht⟩))).card := by
        apply Finset.card_bij (fun c hc =>
          (⟨c.val, (Finset.mem_filter.mp hc).2⟩ : Fin (mu ⟨t, ht⟩)))
        · intro c hc; exact Finset.mem_univ _
        · intro a ha b hb he
          exact Fin.ext (congrArg (fun t : Fin (mu ⟨t, ht⟩) => t.val) he)
        · intro b hb
          refine ⟨⟨b.val, lt_of_lt_of_le b.isLt hle⟩, ?_, ?_⟩
          · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, b.isLt⟩
          · rfl
      _ = _ := Finset.card_fin _
  · have hn (c : Column mu) : ¬t < columnHeight mu c := by
      have := columnHeight_le mu c
      omega
    simp [heightTail, rowAt, ht, hn]

def heightFiber (k : ℕ) : ℕ :=
  (Finset.univ.filter (fun c : Column mu => columnHeight mu c = k)).card

theorem heightFiber_zero_add : heightFiber mu 0 + heightTail mu 0 = ∑ i, mu i := by
  have h : (Finset.univ.filter (fun c : Column mu => columnHeight mu c = 0)).card +
      (Finset.univ.filter (fun c : Column mu => ¬columnHeight mu c = 0)).card =
      (Finset.univ : Finset (Column mu)).card :=
    Finset.card_filter_add_card_filter_not _
  simpa only [← Nat.pos_iff_ne_zero, Finset.card_univ, Fintype.card_fin] using h

theorem heightFiber_succ_add (k : ℕ) :
    heightFiber mu (k + 1) + heightTail mu (k + 1) = heightTail mu k := by
  unfold heightFiber heightTail
  have hs (p : Column mu → Prop) [DecidablePred p] :
      (Finset.univ.filter p).card = ∑ c : Column mu, if p c then 1 else 0 := by
    simpa using (Finset.sum_boole (R := ℕ) p Finset.univ).symm
  rw [hs, hs, hs]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro c _
  split_ifs <;> omega

theorem rowAt_add (nu : Fin d → ℕ) (k : ℕ) : rowAt (mu + nu) k = rowAt mu k + rowAt nu k := by
  unfold rowAt
  split <;> simp

/-- Every column-height multiplicity adds exactly, including height zero. -/
theorem heightFiber_add (nu : Fin d → ℕ) (hmu : Antitone mu) (hnu : Antitone nu) (k : ℕ) :
    heightFiber (mu + nu) k = heightFiber mu k + heightFiber nu k := by
  have hsum : Antitone (mu + nu) := fun i j hij => add_le_add (hmu hij) (hnu hij)
  have ht (k : ℕ) : heightTail (mu + nu) k = heightTail mu k + heightTail nu k := by
    rw [heightTail_eq _ hsum, heightTail_eq _ hmu, heightTail_eq _ hnu, rowAt_add]
  cases k with
  | zero =>
    have ha := heightFiber_zero_add (mu + nu)
    have hb := heightFiber_zero_add mu
    have hc := heightFiber_zero_add nu
    rw [ht] at ha
    simp only [Pi.add_apply, Finset.sum_add_distrib] at ha
    omega
  | succ k =>
    have ha := heightFiber_succ_add (mu + nu) k
    have hb := heightFiber_succ_add mu k
    have hc := heightFiber_succ_add nu k
    rw [ht, ht] at ha
    omega

def sumColumnHeight (nu : Fin d → ℕ) : Column mu ⊕ Column nu → ℕ :=
  Sum.elim (columnHeight mu) (columnHeight nu)

def sumHeightFiberEquiv (nu : Fin d → ℕ) (k : ℕ) :
    {c : Column mu ⊕ Column nu // sumColumnHeight mu nu c = k} ≃
      ({c : Column mu // columnHeight mu c = k} ⊕
        {c : Column nu // columnHeight nu c = k}) where
  toFun x := match x with
    | ⟨.inl c, h⟩ => .inl ⟨c, h⟩
    | ⟨.inr c, h⟩ => .inr ⟨c, h⟩
  invFun x := match x with
    | .inl ⟨c, h⟩ => ⟨.inl c, h⟩
    | .inr ⟨c, h⟩ => ⟨.inr c, h⟩
  left_inv := by rintro ⟨c | c, h⟩ <;> rfl
  right_inv := by rintro (⟨c,h⟩ | ⟨c,h⟩) <;> rfl

theorem column_fiber_card (nu : Fin d → ℕ) (hmu : Antitone mu) (hnu : Antitone nu) (k : ℕ) :
    Fintype.card {c : Column (mu + nu) // columnHeight (mu + nu) c = k} =
      Fintype.card {c : Column mu ⊕ Column nu // sumColumnHeight mu nu c = k} := by
  classical
  rw [Fintype.card_congr (sumHeightFiberEquiv mu nu k), Fintype.card_sum]
  simpa only [Fintype.card_subtype, heightFiber] using heightFiber_add mu nu hmu hnu k

/-- A concrete finite equivalence of actual exterior column factors.
Each factor is sent to one of exactly the same exterior degree. -/
def columnEquiv (nu : Fin d → ℕ) (hmu : Antitone mu) (hnu : Antitone nu) :
    Column (mu + nu) ≃ Column mu ⊕ Column nu :=
  Equiv.ofFiberEquiv (fun k => Fintype.equivOfCardEq (column_fiber_card mu nu hmu hnu k))

theorem columnEquiv_height (nu : Fin d → ℕ) (hmu : Antitone mu) (hnu : Antitone nu)
    (c : Column (mu + nu)) :
    sumColumnHeight mu nu (columnEquiv mu nu hmu hnu c) = columnHeight (mu + nu) c :=
  Equiv.ofFiberEquiv_map _ c

end FreeEntropy.ExteriorRepresentation
