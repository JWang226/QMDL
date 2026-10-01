/-
Copyright (c) 2026 Free Entropy formalization contributors.
See LICENSE and NOTICE in the repository root for license and attribution.
-/

import FreeEntropy.ExteriorWeightMultiplicity
import FreeEntropy.CyclicWeightStates

/-! Simple-root offsets are actual positive-root assignments. This connects
the concrete canonical multiplicity formulas to the offset indexing used
by the quantum cloning estimates. -/
noncomputable section
open scoped BigOperators
namespace FreeEntropy.ExteriorRepresentation
open CasimirWeights CartanLieCloning
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
variable {d : ℕ}

def simpleLowerRoot (j : Fin (d - 1)) : LowerRoot d :=
  ⟨(left j, right j), by change j.val < j.val + 1; omega⟩

def simpleRootAssignment (delta : Fin (d - 1) → ℕ) : LowerRoot d →₀ ℕ :=
  ∑ j, Finsupp.single (simpleLowerRoot j) (delta j)

theorem simpleRootAssignment_depth (delta : Fin (d - 1) → ℕ) :
    rootDepth (simpleRootAssignment delta) = depth delta := by
  classical
  simp only [rootDepth, simpleRootAssignment, Finsupp.finset_sum_apply, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  simp [Finsupp.single_apply, mul_ite, simpleLowerRoot, left, right]

theorem simpleRootAssignment_shift (delta : Fin (d - 1) → ℕ) (k : Fin d) :
    (rootWeightShift (simpleRootAssignment delta) k : ℝ) = -offset delta k := by
  classical
  simp only [rootWeightShift, simpleRootAssignment, Finsupp.finset_sum_apply,
    Nat.cast_sum, Nat.cast_mul, Int.cast_sum, Int.cast_mul, Int.cast_natCast,
    Finset.sum_mul]
  rw [Finset.sum_comm]
  rw [offset, ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro j _
  simp only [Finsupp.single_apply, Nat.cast_ite, Nat.cast_zero, ite_mul, zero_mul]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true]
  simp only [simpleLowerRoot, simpleRoot, Int.cast_sub, Int.cast_ite, Int.cast_one, Int.cast_zero]
  ring

private theorem canonicalWeightModel_card_eq (mu wt : Fin d → ℕ) :
    Fintype.card {a : IrrepIndex mu // (canonicalWeightModel mu).weight a = fun k => (wt k : ℝ)} =
      Fintype.card {a : IrrepIndex mu // canonicalWeight mu a = wt} := by
  classical
  apply Fintype.card_congr
  apply Equiv.subtypeEquivRight
  intro a
  rw [canonicalWeight_spec]
  constructor
  · intro h
    funext k
    exact_mod_cast congrFun h k
  · rintro rfl
    rfl

theorem canonical_offsetMultiplicity_shallow
    (mu : Fin d → ℕ) (hmu : Antitone mu) (g : ℕ)
    (hgap : ∀ j : Fin d, ∀ hj : j.val + 1 < d, g + mu ⟨j.val + 1, hj⟩ ≤ mu j)
    (delta : Fin (d - 1) → ℕ) (hdepth : depth delta ≤ g) :
    (canonicalWeightModel mu).offsetMultiplicity delta =
      (lowerWeightFiber (simpleRootAssignment delta)).card := by
  classical
  let a := simpleRootAssignment delta
  have ha : rootDepth a ≤ g := by simpa only [a, simpleRootAssignment_depth] using hdepth
  let wt := tensorWeight (columnHeight mu) (shallowMonomialBasis mu a hmu g hgap ha)
  have hshift : ∀ k, (wt k : ℤ) - (mu k : ℤ) = rootWeightShift a k :=
    shallowMonomialBasis_weight_difference mu a hmu g hgap ha
  have hwt : (canonicalWeightModel mu).row - offset delta = fun k => (wt k : ℝ) := by
    rw [canonicalWeightModel_row mu hmu]
    funext k
    have he : (wt k : ℝ) - (mu k : ℝ) = (rootWeightShift a k : ℝ) := by exact_mod_cast hshift k
    rw [show (rootWeightShift a k : ℝ) = -offset delta k from simpleRootAssignment_shift delta k] at he
    change (mu k : ℝ) - offset delta k = (wt k : ℝ)
    linarith
  change weightMultiplicity (canonicalWeightModel mu).weight _ = _
  rw [hwt]
  have hc := canonicalWeightModel_card_eq mu wt
  have he := shallow_actualWeight_finrank_eq_rootFiber mu wt hmu g hgap a ha hshift
  rw [← canonicalWeight_card_eq_finrank] at he
  have heq : weightMultiplicity (canonicalWeightModel mu).weight (fun k => (wt k : ℝ)) =
      Fintype.card {b : IrrepIndex mu // canonicalWeight mu b = wt} := by
    simpa only [Fintype.card_subtype, weightMultiplicity] using hc
  exact heq.trans he

end FreeEntropy.ExteriorRepresentation
