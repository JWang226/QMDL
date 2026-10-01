/-
Copyright (c) 2026 Free Entropy formalization contributors.
See LICENSE and NOTICE in the repository root for license and attribution.
-/

import Mathlib.Algebra.Order.Antidiag.FinsuppEquiv
import FreeEntropy.WeylFinite
import FreeEntropy.MeanDepth

/-!
# Counting positive-root assignments by depth

This file proves the coefficient bound used in the mean-depth estimate.
The assignments and their finite sets are constructed explicitly. The
injection into ordinary stars-and-bars assignments is proved, not assumed.
The connection from a representation's weight multiplicities to root
partition fibers (the PBW/Verma spanning argument) remains a separate input.
-/

noncomputable section
open scoped BigOperators

namespace FreeEntropy.KostantCounting

variable {ι κ : Type*} [DecidableEq ι]

/-- Weighted depth of a nonnegative integer assignment to a finite root set. -/
def weightedDepth (roots : Finset ι) (height : ι → ℕ) (c : ι →₀ ℕ) : ℕ :=
  ∑ i ∈ roots, height i * c i

/-- All assignments supported on `roots`, of ordinary degree at most `t`,
whose weighted depth is exactly `t`. Positive heights make the degree bound
automatic, as the membership theorem below proves. -/
def weightedAssignments (roots : Finset ι) (height : ι → ℕ) (t : ℕ) : Finset (ι →₀ ℕ) :=
  ((Finset.range (t + 1)).biUnion (fun n => roots.finsuppAntidiag n)).filter
    (fun c => weightedDepth roots height c = t)

omit [DecidableEq ι] in
theorem ordinaryDegree_le_weightedDepth (roots : Finset ι) (height : ι → ℕ)
    (hheight : ∀ i ∈ roots, 0 < height i) (c : ι →₀ ℕ) :
    (∑ i ∈ roots, c i) ≤ weightedDepth roots height c := by
  apply Finset.sum_le_sum
  intro i hi
  calc
    c i = 1 * c i := (one_mul _).symm
    _ ≤ height i * c i := Nat.mul_le_mul_right _ (hheight i hi)

theorem weightedDepth_eq_zero_iff (roots : Finset ι) (height : ι → ℕ)
    (hheight : ∀ i ∈ roots, 0 < height i) (c : ι →₀ ℕ)
    (hsupport : c.support ⊆ roots) : weightedDepth roots height c = 0 ↔ c = 0 := by
  constructor
  · intro hzero
    apply Finsupp.ext
    intro i
    by_cases hi : i ∈ roots
    · have hsum : ∀ j ∈ roots, height j * c j = 0 := by
        simpa only [weightedDepth, Finset.sum_eq_zero_iff] using hzero
      have hc := (mul_eq_zero.mp (hsum i hi)).resolve_left (hheight i hi).ne'
      exact hc
    · exact Finsupp.notMem_support_iff.mp (fun h => hi (hsupport h))
  · rintro rfl
    simp [weightedDepth]

theorem mem_weightedAssignments (roots : Finset ι) (height : ι → ℕ)
    (hheight : ∀ i ∈ roots, 0 < height i) (t : ℕ) (c : ι →₀ ℕ) :
    c ∈ weightedAssignments roots height t ↔
      c.support ⊆ roots ∧ weightedDepth roots height c = t := by
  constructor
  · intro hc
    obtain ⟨hc, hweight⟩ := Finset.mem_filter.mp hc
    obtain ⟨n, _, hn⟩ := Finset.mem_biUnion.mp hc
    exact ⟨(Finset.mem_finsuppAntidiag.mp hn).2, hweight⟩
  · rintro ⟨hsupport, hweight⟩
    apply Finset.mem_filter.mpr
    refine ⟨?_, hweight⟩
    apply Finset.mem_biUnion.mpr
    refine ⟨∑ i ∈ roots, c i, ?_, Finset.mem_finsuppAntidiag.mpr ⟨rfl, hsupport⟩⟩
    apply Finset.mem_range.mpr
    have h := ordinaryDegree_le_weightedDepth roots height hheight c
    omega

/-- Put the excess weighted depth into one distinguished root coordinate. -/
def padAssignment (roots : Finset ι) (k : ι) (t : ℕ) (c : ι →₀ ℕ) : ι →₀ ℕ :=
  c + Finsupp.single k (t - ∑ i ∈ roots, c i)

omit [DecidableEq ι] in
theorem padAssignment_apply_ne (roots : Finset ι) (k : ι) (t : ℕ) (c : ι →₀ ℕ)
    (i : ι) (hi : i ≠ k) : padAssignment roots k t c i = c i := by
  simp [padAssignment, hi]

theorem padAssignment_mem_antidiag (roots : Finset ι) (height : ι → ℕ)
    (hheight : ∀ i ∈ roots, 0 < height i) (k : ι) (hk : k ∈ roots) (t : ℕ)
    (c : ι →₀ ℕ) (hc : c ∈ weightedAssignments roots height t) :
    padAssignment roots k t c ∈ roots.finsuppAntidiag t := by
  obtain ⟨hsupport, hweight⟩ := (mem_weightedAssignments roots height hheight t c).mp hc
  have hdegree : (∑ i ∈ roots, c i) ≤ t := by
    simpa only [hweight] using ordinaryDegree_le_weightedDepth roots height hheight c
  apply Finset.mem_finsuppAntidiag.mpr
  constructor
  · simp only [padAssignment, Finsupp.coe_add, Pi.add_apply, Finset.sum_add_distrib]
    have hsingle : (∑ x ∈ roots, (Finsupp.single k (t - ∑ i ∈ roots, c i)) x) =
        t - ∑ i ∈ roots, c i := by
      rw [Finset.sum_eq_single k]
      · exact Finsupp.single_eq_same
      · intro i _ hik
        exact Finsupp.single_eq_of_ne hik
      · exact fun hnot => (hnot hk).elim
    rw [hsingle]
    exact Nat.add_sub_of_le hdegree
  · intro i hi
    by_contra hiroots
    have hci : c i = 0 := Finsupp.notMem_support_iff.mp (fun himem => hiroots (hsupport himem))
    have hik : i ≠ k := fun heq => hiroots (heq ▸ hk)
    have hz : padAssignment roots k t c i = 0 := by rw [padAssignment_apply_ne _ _ _ _ _ hik, hci]
    exact (Finsupp.mem_support_iff.mp hi) hz

/-- Equal padded tuples recover the original tuple: all other coordinates
are unchanged, and equal weighted depths recover the distinguished one. -/
theorem padAssignment_injective_on (roots : Finset ι) (height : ι → ℕ)
    (hheight : ∀ i ∈ roots, 0 < height i) (k : ι) (hk : k ∈ roots) (t : ℕ) :
    Set.InjOn (padAssignment roots k t) (weightedAssignments roots height t : Set (ι →₀ ℕ)) := by
  intro c hc d hd hpad
  have hoff (i : ι) (hik : i ≠ k) : c i = d i := by
    have h := congrArg (fun f : ι →₀ ℕ => f i) hpad
    simpa only [padAssignment_apply_ne _ _ _ _ _ hik] using h
  have hcweight := ((mem_weightedAssignments roots height hheight t c).mp hc).2
  have hdweight := ((mem_weightedAssignments roots height hheight t d).mp hd).2
  have hrest : (∑ i ∈ roots.erase k, height i * c i) = ∑ i ∈ roots.erase k, height i * d i := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [hoff i (Finset.mem_erase.mp hi).1]
  have hsumc := (Finset.sum_erase_add roots (fun i => height i * c i) hk).trans hcweight
  have hsumd := (Finset.sum_erase_add roots (fun i => height i * d i) hk).trans hdweight
  have hkval : c k = d k := by
    apply Nat.eq_of_mul_eq_mul_left (hheight k hk)
    omega
  apply Finsupp.ext
  intro i
  by_cases hi : i = k
  · simpa only [hi] using hkval
  · exact hoff i hi

/-- Coefficient domination by the ordinary `N`-variable geometric series.
This proves the exact binomial bound for the actual assignment cardinality. -/
theorem card_weightedAssignments_le (roots : Finset ι) (height : ι → ℕ)
    (hheight : ∀ i ∈ roots, 0 < height i) (k : ι) (hk : k ∈ roots) (t : ℕ) :
    (weightedAssignments roots height t).card ≤ (t + roots.card - 1).choose (roots.card - 1) := by
  calc
    _ ≤ (roots.finsuppAntidiag t).card :=
      Finset.card_le_card_of_injOn (padAssignment roots k t)
        (fun c hc => padAssignment_mem_antidiag roots height hheight k hk t c hc)
        (padAssignment_injective_on roots height hheight k hk t)
    _ = (roots.card + t - 1).choose t := Finset.card_finsuppAntidiag_nat_eq_choose t
    _ = _ := by
      have hpos : 0 < roots.card := Finset.card_pos.mpr ⟨k, hk⟩
      rw [Nat.add_comm roots.card t]
      apply Nat.choose_symm_of_eq_add
      omega

/-- Type-A positive roots carry their actual simple-root heights `j-i`. -/
def positiveRootAssignments (r t : ℕ) : Finset ((ℕ × ℕ) →₀ ℕ) :=
  weightedAssignments (Weyl.activeRoots r r) (fun p => p.2 - p.1) t

theorem card_positiveRootAssignments_le (r t : ℕ) (hr : 2 ≤ r) :
    (positiveRootAssignments r t).card ≤ (t + r.choose 2 - 1).choose (r.choose 2 - 1) := by
  have hh : ∀ p ∈ Weyl.activeRoots r r, 0 < p.2 - p.1 :=
    fun p hp => Nat.sub_pos_of_lt (Weyl.mem_activeRoots.mp hp).2.1
  have hk : (0, 1) ∈ Weyl.activeRoots r r := by
    rw [Weyl.mem_activeRoots]
    omega
  have hcard : (Weyl.activeRoots r r).card = r.choose 2 := by exact_mod_cast Weyl.all_root_count r
  simpa only [positiveRootAssignments, hcard] using
    card_weightedAssignments_le (Weyl.activeRoots r r) _ hh (0, 1) hk t

/-- Simple-root coefficients, expressed as cuts between consecutive rows.
The root `(i,j)` crosses precisely the cuts `i < k ≤ j`. -/
def typeAOffset (r : ℕ) (c : (ℕ × ℕ) →₀ ℕ) (k : ℕ) : ℕ :=
  ∑ p ∈ Weyl.activeRoots r r, if p.1 < k ∧ k ≤ p.2 then c p else 0

@[simp] theorem typeAOffset_zero (r : ℕ) (c : (ℕ × ℕ) →₀ ℕ) :
    typeAOffset r c 0 = 0 := by simp [typeAOffset]

theorem typeAOffset_eq_zero_of_le (r : ℕ) (c : (ℕ × ℕ) →₀ ℕ) (k : ℕ)
    (hrk : r ≤ k) : typeAOffset r c k = 0 := by
  apply Finset.sum_eq_zero
  intro p hp
  have hp' := Weyl.mem_activeRoots.mp hp
  have hfalse : ¬(p.1 < k ∧ k ≤ p.2) := by omega
  simp only [if_neg hfalse]

/-- Sum of all simple-root coefficients, including the vanishing boundary cuts. -/
def offsetDepth (r : ℕ) (δ : ℕ → ℕ) : ℕ := ∑ k ∈ Finset.range (r + 1), δ k

theorem offsetDepth_typeAOffset (r : ℕ) (c : (ℕ × ℕ) →₀ ℕ) :
    offsetDepth r (typeAOffset r c) =
      weightedDepth (Weyl.activeRoots r r) (fun p => p.2 - p.1) c := by
  unfold offsetDepth typeAOffset weightedDepth
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro p hp
  have hp' := Weyl.mem_activeRoots.mp hp
  have hfilter : (Finset.range (r + 1)).filter (fun k => p.1 < k ∧ k ≤ p.2) =
      Finset.Ioc p.1 p.2 := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ioc]
    omega
  rw [← Finset.sum_filter, hfilter]
  simp

/-- The `r-1` nontrivial cut coefficients have the expected total depth. -/
theorem sum_simple_cuts (r : ℕ) (hr : 0 < r) (c : (ℕ × ℕ) →₀ ℕ) :
    (∑ j ∈ Finset.range (r - 1), typeAOffset r c (j + 1)) =
      weightedDepth (Weyl.activeRoots r r) (fun p => p.2 - p.1) c := by
  have h := offsetDepth_typeAOffset r c
  unfold offsetDepth at h
  rw [Finset.sum_range_succ, typeAOffset_eq_zero_of_le r c r le_rfl, Nat.add_zero] at h
  have hr' : r - 1 + 1 = r := by omega
  have hsum := Finset.sum_range_succ' (typeAOffset r c) (r - 1)
  rw [hr', typeAOffset_zero, Nat.add_zero] at hsum
  exact hsum.symm.trans h

/-- The actual finite Kostant partition fiber for a prescribed cut offset. -/
def kostantFiber (r : ℕ) (δ : ℕ → ℕ) : Finset ((ℕ × ℕ) →₀ ℕ) := by
  classical
  exact (positiveRootAssignments r (offsetDepth r δ)).filter (fun c => typeAOffset r c = δ)

def kostantCount (r : ℕ) (δ : ℕ → ℕ) : ℕ := (kostantFiber r δ).card

theorem mem_kostantFiber (r : ℕ) (δ : ℕ → ℕ) (c : (ℕ × ℕ) →₀ ℕ) :
    c ∈ kostantFiber r δ ↔ c.support ⊆ Weyl.activeRoots r r ∧ typeAOffset r c = δ := by
  classical
  have hh : ∀ p ∈ Weyl.activeRoots r r, 0 < p.2 - p.1 :=
    fun p hp => Nat.sub_pos_of_lt (Weyl.mem_activeRoots.mp hp).2.1
  simp only [kostantFiber, Finset.mem_filter, positiveRootAssignments,
    mem_weightedAssignments _ _ hh]
  constructor
  · exact fun h => ⟨h.1.1, h.2⟩
  · rintro ⟨hsupport, hoffset⟩
    refine ⟨⟨hsupport, ?_⟩, hoffset⟩
    rw [← offsetDepth_typeAOffset, hoffset]

/-- A finite basis encoded injectively by genuine root assignments inherits
the depth-layer bound. Both support and depth are checked for each encoding. -/
theorem card_depth_fiber_le_of_encoding {β : Type*} [DecidableEq β]
    (s : Finset β) (depth : β → ℕ) (encode : β → (ι →₀ ℕ))
    (roots : Finset ι) (height : ι → ℕ) (hheight : ∀ i ∈ roots, 0 < height i)
    (k : ι) (hk : k ∈ roots)
    (hinj : Set.InjOn encode (s : Set β))
    (hsupport : ∀ b ∈ s, (encode b).support ⊆ roots)
    (hdepth : ∀ b ∈ s, weightedDepth roots height (encode b) = depth b) (t : ℕ) :
    (s.filter (fun b => depth b = t)).card ≤ (t + roots.card - 1).choose (roots.card - 1) := by
  calc
    _ ≤ (weightedAssignments roots height t).card := by
      apply Finset.card_le_card_of_injOn encode
      · intro b hb
        obtain ⟨hbs, hbt⟩ := Finset.mem_filter.mp hb
        apply (mem_weightedAssignments roots height hheight t (encode b)).mpr
        exact ⟨hsupport b hbs, (hdepth b hbs).trans hbt⟩
      · exact hinj.mono (fun _ h => (Finset.mem_filter.mp h).1)
    _ ≤ _ := card_weightedAssignments_le roots height hheight k hk t

theorem card_typeA_depth_fiber_le_of_encoding {β : Type*} [DecidableEq β]
    (s : Finset β) (depth : β → ℕ) (encode : β → ((ℕ × ℕ) →₀ ℕ))
    (r : ℕ) (hr : 2 ≤ r)
    (hinj : Set.InjOn encode (s : Set β))
    (hsupport : ∀ b ∈ s, (encode b).support ⊆ Weyl.activeRoots r r)
    (hdepth : ∀ b ∈ s,
      weightedDepth (Weyl.activeRoots r r) (fun p => p.2 - p.1) (encode b) = depth b)
    (t : ℕ) :
    (s.filter (fun b => depth b = t)).card ≤ (t + r.choose 2 - 1).choose (r.choose 2 - 1) := by
  have hh : ∀ p ∈ Weyl.activeRoots r r, 0 < p.2 - p.1 :=
    fun p hp => Nat.sub_pos_of_lt (Weyl.mem_activeRoots.mp hp).2.1
  have hk : (0, 1) ∈ Weyl.activeRoots r r := by
    rw [Weyl.mem_activeRoots]
    omega
  have hcard : (Weyl.activeRoots r r).card = r.choose 2 := by exact_mod_cast Weyl.all_root_count r
  simpa only [hcard] using card_depth_fiber_le_of_encoding s depth encode
    (Weyl.activeRoots r r) _ hh (0, 1) hk hinj hsupport hdepth t

/-- Distinct weight offsets have disjoint assignment fibers. Consequently
individual PBW/Verma multiplicity bounds imply the required depth-layer
envelope; no separate injection or aggregate coefficient bound is assumed. -/
theorem sum_fiber_multiplicities_le [DecidableEq κ]
    (roots : Finset ι) (height : ι → ℕ) (hheight : ∀ i ∈ roots, 0 < height i)
    (k : ι) (hk : k ∈ roots) (t : ℕ) (offsets : Finset κ)
    (offset : (ι →₀ ℕ) → κ) (multiplicity : κ → ℕ)
    (hPBW : ∀ δ ∈ offsets, multiplicity δ ≤
      ((weightedAssignments roots height t).filter (fun c => offset c = δ)).card) :
    ∑ δ ∈ offsets, multiplicity δ ≤ (t + roots.card - 1).choose (roots.card - 1) := by
  calc
    _ ≤ ∑ δ ∈ offsets, ((weightedAssignments roots height t).filter (fun c => offset c = δ)).card :=
      Finset.sum_le_sum hPBW
    _ = ((weightedAssignments roots height t).filter (fun c => offset c ∈ offsets)).card :=
      Finset.sum_card_fiberwise_eq_card_filter _ _ _
    _ ≤ (weightedAssignments roots height t).card := Finset.card_filter_le _ _
    _ ≤ _ := card_weightedAssignments_le roots height hheight k hk t

/-- Individual multiplicities bounded by actual Kostant fibers give the
coefficient envelope needed in Theorem 2. The disjointness across offsets
and the root-partition count are both proved here. -/
theorem sum_multiplicities_at_depth_le (r : ℕ) (hr : 2 ≤ r)
    (offsets : Finset (ℕ → ℕ)) (multiplicity : (ℕ → ℕ) → ℕ)
    (hPBW : ∀ δ ∈ offsets, multiplicity δ ≤ kostantCount r δ) (t : ℕ) :
    ∑ δ ∈ offsets with offsetDepth r δ = t, multiplicity δ ≤
      (t + r.choose 2 - 1).choose (r.choose 2 - 1) := by
  classical
  have hh : ∀ p ∈ Weyl.activeRoots r r, 0 < p.2 - p.1 :=
    fun p hp => Nat.sub_pos_of_lt (Weyl.mem_activeRoots.mp hp).2.1
  have hk : (0, 1) ∈ Weyl.activeRoots r r := by
    rw [Weyl.mem_activeRoots]
    omega
  have hcard : (Weyl.activeRoots r r).card = r.choose 2 := by exact_mod_cast Weyl.all_root_count r
  have h := sum_fiber_multiplicities_le (Weyl.activeRoots r r)
    (fun p => p.2 - p.1) hh (0, 1) hk t
    (offsets.filter (fun δ => offsetDepth r δ = t)) (typeAOffset r) multiplicity (by
      intro δ hδ
      obtain ⟨hδs, hδt⟩ := Finset.mem_filter.mp hδ
      simpa only [kostantCount, kostantFiber, hδt, positiveRootAssignments] using hPBW δ hδs)
  simpa only [hcard] using h

theorem sum_kostantCount_at_depth_le (r : ℕ) (hr : 2 ≤ r)
    (offsets : Finset (ℕ → ℕ)) (t : ℕ) :
    ∑ δ ∈ offsets with offsetDepth r δ = t, kostantCount r δ ≤
      (t + r.choose 2 - 1).choose (r.choose 2 - 1) :=
  sum_multiplicities_at_depth_le r hr offsets (kostantCount r) (fun _ _ => le_rfl) t

/-- The paper's exact mean-depth constant, now requiring only the local
PBW spanning bound and the spectral monomial envelope. The previously
separate aggregate coefficient-counting hypothesis is discharged. -/
theorem weight_mean_le_of_kostant (r : ℕ) (hr : 2 ≤ r)
    (offsets : Finset (ℕ → ℕ)) (multiplicity : (ℕ → ℕ) → ℕ)
    (p : (ℕ → ℕ) → ℝ) (q : ℝ) (hq : 0 ≤ q) (hq1 : q < 1)
    (hPBW : ∀ δ ∈ offsets, multiplicity δ ≤ kostantCount r δ)
    (hp : ∀ δ ∈ offsets, p δ ≤ q ^ offsetDepth r δ) :
    ∑ δ ∈ offsets, (offsetDepth r δ : ℝ) * p δ * (multiplicity δ : ℝ) ≤
      MeanDepth.meanDepthConstant (r.choose 2) q := by
  have hN : 0 < r.choose 2 := Nat.choose_pos hr
  exact MeanDepth.weight_mean_le offsets (offsetDepth r) multiplicity p (r.choose 2)
    hN q hq hq1 hp (sum_multiplicities_at_depth_le r hr offsets multiplicity hPBW)

end FreeEntropy.KostantCounting
