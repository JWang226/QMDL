/-
Copyright (c) 2026 Free Entropy formalization contributors.
See LICENSE and NOTICE in the repository root for license and attribution.
-/

import FreeEntropy.ExteriorMonomialWeights
import FreeEntropy.KostantCounting

/-! Shallow monomials use only gaps at the roots actually present. This includes
rank-deficient highest weights with a zero tail. Root depth is determined by
the actual signed weight change, and its fibers are constructed finite sets. -/
noncomputable section
open scoped BigOperators
namespace FreeEntropy.ExteriorRepresentation
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
variable {d : ℕ}

def rootNext (r : LowerRoot d) : Fin d :=
  ⟨r.val.1.val + 1, by have hr : r.val.1.val < r.val.2.val := r.property; have := r.val.2.isLt; omega⟩

variable (mu : Fin d → ℕ) (a : LowerRoot d →₀ ℕ)

theorem supported_root_capacity (hmu : Antitone mu) (g : ℕ)
    (hgap : ∀ r : LowerRoot d, a r ≠ 0 → g + mu (rootNext r) ≤ mu r.val.1)
    (hdepth : rootDepth a ≤ g) (k : ℕ) :
    Fintype.card {x : RootCopies a // rootCopyHeight a x = k} ≤ heightFiber mu k := by
  classical
  by_cases hn : Nonempty {x : RootCopies a // rootCopyHeight a x = k}
  · obtain ⟨⟨x, hx⟩⟩ := hn
    have hax : a x.1 ≠ 0 := by have := x.2.isLt; omega
    have hg := hgap x.1 hax
    have hf := heightFiber_adjacent mu hmu x.1.val.1 (rootNext x.1).isLt
    have hc := Fintype.card_subtype_le (fun x : RootCopies a => rootCopyHeight a x = k)
    have hd := rootCopies_card_le_depth a
    change x.1.val.1.val + 1 = k at hx
    have hfg : g ≤ heightFiber mu (x.1.val.1.val + 1) := by
      change g + mu ⟨_, _⟩ ≤ _ at hg
      omega
    rw [hx] at hfg
    omega
  · haveI : IsEmpty {x : RootCopies a // rootCopyHeight a x = k} := not_nonempty_iff.mp hn
    simp

def supportedMonomialBasis (hmu : Antitone mu) (g : ℕ)
    (hgap : ∀ r : LowerRoot d, a r ≠ 0 → g + mu (rootNext r) ≤ mu r.val.1)
    (hdepth : rootDepth a ≤ g) : AmbientIndex mu :=
  monomialBasis mu a (supported_root_capacity mu a hmu g hgap hdepth)

theorem supportedMonomialBasis_coefficient (hmu : Antitone mu) (g : ℕ)
    (hgap : ∀ r : LowerRoot d, a r ≠ 0 → g + mu (rootNext r) ≤ mu r.val.1)
    (hdepth : rootDepth a ≤ g) (x : LowerRoot d → ℂ) :
    tensorMatrix (columnHeight mu) (lowerRootMatrix x)
      (supportedMonomialBasis mu a hmu g hgap hdepth) (highestBasisIndex mu) =
      ∏ r : LowerRoot d, x r ^ a r := by
  rw [supportedMonomialBasis, monomialBasis_coefficient mu a _ _
    (lowerRootMatrix_upper x) (lowerRootMatrix_diagonal x)]
  simp only [lowerRootMatrix_root]

theorem supportedMonomialBasis_weight_difference (hmu : Antitone mu) (g : ℕ)
    (hgap : ∀ r : LowerRoot d, a r ≠ 0 → g + mu (rootNext r) ≤ mu r.val.1)
    (hdepth : rootDepth a ≤ g) (k : Fin d) :
    (tensorWeight (columnHeight mu) (supportedMonomialBasis mu a hmu g hgap hdepth) k : ℤ) -
      (mu k : ℤ) = rootWeightShift a k :=
  monomialBasis_weight_difference mu a hmu _ k

/-- The signed weight shift records exactly the root-height degree. -/
theorem rootDepth_eq_weightShift : (rootDepth a : ℤ) =
    ∑ k : Fin d, (k.val : ℤ) * rootWeightShift a k := by
  simp only [rootDepth, Nat.cast_sum, Nat.cast_mul, rootWeightShift, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro r _
  have hle : r.val.1.val ≤ r.val.2.val := le_of_lt r.property
  rw [Nat.cast_sub hle]
  simp only [mul_sub, mul_ite, mul_one, mul_zero, Finset.sum_sub_distrib]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
  ring

theorem rootDepth_eq_of_weightShift_eq (b : LowerRoot d →₀ ℕ)
    (h : rootWeightShift a = rootWeightShift b) : rootDepth a = rootDepth b := by
  have he : (rootDepth a : ℤ) = (rootDepth b : ℤ) := by
    rw [rootDepth_eq_weightShift, rootDepth_eq_weightShift, h]
  exact_mod_cast he

/-- The actual finite depth layer of positive-root assignments. -/
def lowerAssignmentsAtDepth (t : ℕ) : Finset (LowerRoot d →₀ ℕ) :=
  KostantCounting.weightedAssignments Finset.univ (fun r => r.val.2.val - r.val.1.val) t

theorem mem_lowerAssignmentsAtDepth (t : ℕ) : a ∈ lowerAssignmentsAtDepth (d := d) t ↔ rootDepth a = t := by
  have hh : ∀ r : LowerRoot d, r ∈ Finset.univ → 0 < r.val.2.val - r.val.1.val := by
    intro r _; exact Nat.sub_pos_of_lt r.property
  simp only [lowerAssignmentsAtDepth, KostantCounting.mem_weightedAssignments _ _ hh,
    Finset.subset_univ, true_and, KostantCounting.weightedDepth, rootDepth]

/-- All assignments with the same actual signed weight change, as a finite set. -/
def lowerWeightFiber : Finset (LowerRoot d →₀ ℕ) :=
  (lowerAssignmentsAtDepth (rootDepth a)).filter (fun b => rootWeightShift b = rootWeightShift a)

theorem mem_lowerWeightFiber (b : LowerRoot d →₀ ℕ) :
    b ∈ lowerWeightFiber a ↔ rootWeightShift b = rootWeightShift a := by
  simp only [lowerWeightFiber, Finset.mem_filter, mem_lowerAssignmentsAtDepth]
  exact ⟨fun h => h.2, fun h => ⟨rootDepth_eq_of_weightShift_eq b a h, h⟩⟩

end FreeEntropy.ExteriorRepresentation
