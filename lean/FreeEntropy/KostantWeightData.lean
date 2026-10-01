/-
Copyright (c) 2026 Free Entropy formalization contributors.
See LICENSE and NOTICE in the repository root for license and attribution.
-/

import FreeEntropy.GeometricOrbit
import FreeEntropy.KostantCounting

/-!
# Concrete geometric weight data from root assignments

An injective root-partition encoding of a finite basis constructs the actual
weight distribution and discharges its counting and spectral-envelope fields.
The adjacent eigenvalue ratios are indexed from zero; cut `j+1` is the
coefficient of the corresponding simple root. No multiplicity envelope is
assumed in the constructor.
-/

noncomputable section
open scoped BigOperators

namespace FreeEntropy.KostantWeightData

open KostantCounting

/-- The actual eigenvalue monomial of the root offset, relative to the
highest weight. Boundary cuts are omitted. -/
def rootWeight (r : ℕ) (ratio : ℕ → ℝ) (c : (ℕ × ℕ) →₀ ℕ) : ℝ :=
  ∏ j ∈ Finset.range (r - 1), ratio j ^ typeAOffset r c (j + 1)

@[simp] theorem rootWeight_zero (r : ℕ) (ratio : ℕ → ℝ) :
    rootWeight r ratio 0 = 1 := by simp [rootWeight, typeAOffset]

theorem rootWeight_nonneg (r : ℕ) (ratio : ℕ → ℝ)
    (hratio : ∀ j < r - 1, 0 ≤ ratio j) (c : (ℕ × ℕ) →₀ ℕ) :
    0 ≤ rootWeight r ratio c :=
  Finset.prod_nonneg (fun j hj => pow_nonneg (hratio j (Finset.mem_range.mp hj)) _)

theorem rootWeight_le_depth (r : ℕ) (hr : 0 < r) (ratio : ℕ → ℝ) (q : ℝ)
    (hratio : ∀ j < r - 1, 0 ≤ ratio j)
    (hbound : ∀ j < r - 1, ratio j ≤ q) (c : (ℕ × ℕ) →₀ ℕ) :
    rootWeight r ratio c ≤
      q ^ weightedDepth (Weyl.activeRoots r r) (fun p => p.2 - p.1) c := by
  have h := MeanDepth.root_monomial_le (Finset.range (r - 1))
    (fun j => typeAOffset r c (j + 1)) ratio q
    (fun j hj => hratio j (Finset.mem_range.mp hj))
    (fun j hj => hbound j (Finset.mem_range.mp hj))
  simpa only [rootWeight, sum_simple_cuts r hr c] using h

/-- Construct all geometric weight data from an actual injective encoding
by positive-root assignments. The count bound is stars and bars applied to
that encoding, and the unique zero assignment gives the highest weight. -/
def ofRootEncoding {β : Type*} [Fintype β] [DecidableEq β]
    (r : ℕ) (hr : 2 ≤ r) (q : ℝ)
    (encode : β → ((ℕ × ℕ) →₀ ℕ)) (hinj : Function.Injective encode)
    (hsupport : ∀ b, (encode b).support ⊆ Weyl.activeRoots r r)
    (highest : β) (hhighest : encode highest = 0)
    (ratio : ℕ → ℝ) (hratio : ∀ j < r - 1, 0 ≤ ratio j)
    (hbound : ∀ j < r - 1, ratio j ≤ q) :
    GeometricOrbit.WeightData β (r.choose 2) q where
  weight b := rootWeight r ratio (encode b)
  depth b := weightedDepth (Weyl.activeRoots r r) (fun p => p.2 - p.1) (encode b)
  highest := highest
  nonneg b := rootWeight_nonneg r ratio hratio (encode b)
  highest_weight := by rw [hhighest, rootWeight_zero]
  other_depth b hb := by
    have hh : ∀ p ∈ Weyl.activeRoots r r, 0 < p.2 - p.1 :=
      fun p hp => Nat.sub_pos_of_lt (Weyl.mem_activeRoots.mp hp).2.1
    have hencode : encode b ≠ 0 := fun hz => hb (hinj (hz.trans hhighest.symm))
    have hne := mt (weightedDepth_eq_zero_iff (Weyl.activeRoots r r)
      (fun p => p.2 - p.1) hh (encode b) (hsupport b)).mp hencode
    omega
  envelope b := rootWeight_le_depth r (by omega) ratio q hratio hbound (encode b)
  count t := by
    simpa using card_typeA_depth_fiber_le_of_encoding Finset.univ
      (fun b => weightedDepth (Weyl.activeRoots r r) (fun p => p.2 - p.1) (encode b))
      encode r hr (fun _ _ _ _ h => hinj h) (fun b _ => hsupport b) (fun _ _ => rfl) t

end FreeEntropy.KostantWeightData
