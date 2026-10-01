/-
Copyright (c) 2026 Free Entropy formalization contributors.
See LICENSE and NOTICE in the repository root for license and attribution.
-/

import FreeEntropy.ExteriorSupportedMonomials

/-! Exact finite positive-root counts and the binomial coefficient envelope
for the root assignments occurring in the constructed representations. -/
noncomputable section
open scoped BigOperators
namespace FreeEntropy.ExteriorRepresentation
set_option backward.isDefEq.respectTransparency false
variable {d : ℕ}

def lowerRootNatEquiv : LowerRoot d ≃ {p : ℕ × ℕ // p ∈ Weyl.activeRoots d d} where
  toFun r := ⟨(r.val.1.val, r.val.2.val), Weyl.mem_activeRoots.mpr
    ⟨r.val.1.isLt, r.property, r.val.2.isLt⟩⟩
  invFun p := ⟨(⟨p.val.1, (Weyl.mem_activeRoots.mp p.property).1⟩,
    ⟨p.val.2, (Weyl.mem_activeRoots.mp p.property).2.2⟩),
    (Weyl.mem_activeRoots.mp p.property).2.1⟩
  left_inv r := by rfl
  right_inv p := by rfl

theorem card_lowerRoot : Fintype.card (LowerRoot d) = d.choose 2 := by
  rw [Fintype.card_congr (lowerRootNatEquiv (d := d)), Fintype.card_coe]
  exact_mod_cast Weyl.all_root_count d

theorem card_lowerAssignmentsAtDepth_le (hd : 2 ≤ d) (t : ℕ) :
    (lowerAssignmentsAtDepth (d := d) t).card ≤
      (t + d.choose 2 - 1).choose (d.choose 2 - 1) := by
  let k : LowerRoot d := ⟨(⟨0, by omega⟩, ⟨1, by omega⟩), by change (0 : ℕ) < 1; omega⟩
  have h := KostantCounting.card_weightedAssignments_le
    (Finset.univ : Finset (LowerRoot d)) (fun r => r.val.2.val - r.val.1.val)
    (fun r _ => Nat.sub_pos_of_lt r.property) k (Finset.mem_univ _) t
  simpa only [lowerAssignmentsAtDepth, Finset.card_univ, card_lowerRoot] using h

/-- Distinct equal-weight root fibers partition a depth layer; hence their
actual summed cardinality obeys the same coefficient bound. -/
theorem sum_lowerWeightFiber_at_depth_le (hd : 2 ≤ d)
    {B : Type*} [Fintype B] [DecidableEq B] (a : B → LowerRoot d →₀ ℕ)
    (hinj : Function.Injective (fun b => rootWeightShift (a b))) (t : ℕ) :
    (∑ b : B with rootDepth (a b) = t, (lowerWeightFiber (a b)).card) ≤
      (t + d.choose 2 - 1).choose (d.choose 2 - 1) := by
  classical
  have hdj : (↑(Finset.univ.filter (fun b : B => rootDepth (a b) = t)) : Set B).PairwiseDisjoint
      (fun b => lowerWeightFiber (a b)) := by
    intro b hb c hc hbc
    apply Finset.disjoint_left.mpr
    intro x hx hy
    have hx' := (mem_lowerWeightFiber (a b) x).mp hx
    have hy' := (mem_lowerWeightFiber (a c) x).mp hy
    exact hbc (hinj (hx'.symm.trans hy'))
  rw [← Finset.card_biUnion hdj]
  apply (Finset.card_le_card ?_).trans (card_lowerAssignmentsAtDepth_le hd t)
  intro x hx
  obtain ⟨b, hb, hxb⟩ := Finset.mem_biUnion.mp hx
  apply (mem_lowerAssignmentsAtDepth x t).mpr
  exact (rootDepth_eq_of_weightShift_eq x (a b) ((mem_lowerWeightFiber (a b) x).mp hxb)).trans
    (Finset.mem_filter.mp hb).2

end FreeEntropy.ExteriorRepresentation
