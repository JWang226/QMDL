/-
Copyright (c) 2026 Free Entropy formalization contributors.
See LICENSE and NOTICE in the repository root for license and attribution.
-/

import FreeEntropy.LiePBWOrderedLowering
import FreeEntropy.HighestWeightDominance

/-! Actual PBW upper bounds on weight multiplicities. Ordered lowering words
are indexed injectively by finite root-assignment fibers; projection onto a
joint weight removes all words with the wrong actual weight. -/
noncomputable section
open Matrix
open scoped BigOperators
namespace FreeEntropy.LiePBW
open LieMatrixCasimir ExteriorRepresentation
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
set_option linter.unusedSectionVars false
variable {d : ℕ} {H : Type*} [Fintype H] [DecidableEq H]

theorem lowerExponent_nil : lowerExponent ([] : List (LowerRoot d)) = 0 := by
  simp [lowerExponent]

theorem lowerExponent_cons (r : LowerRoot d) (l : List (LowerRoot d)) :
    lowerExponent (r :: l) = Finsupp.single r 1 + lowerExponent l := by
  change (({r} : Multiset (LowerRoot d)) + (l : Multiset (LowerRoot d))).toFinsupp = _
  rw [map_add, Multiset.toFinsupp_singleton]
  rfl

theorem rootWeightShift_add (a b : LowerRoot d →₀ ℕ) :
    rootWeightShift (a + b) = rootWeightShift a + rootWeightShift b := by
  ext k
  simp [rootWeightShift, Finsupp.add_apply, Nat.cast_add, add_mul, Finset.sum_add_distrib]

theorem rootWeightShift_single (r : LowerRoot d) :
    rootWeightShift (Finsupp.single r 1) =
      fun k => (if k = r.val.2 then 1 else 0) - (if k = r.val.1 then 1 else 0) := by
  ext k
  classical
  simp [rootWeightShift, Finsupp.single_apply]

def shiftedWeight (lam : Fin d → ℂ) (a : LowerRoot d →₀ ℕ) : Fin d → ℂ :=
  fun k => lam k + (rootWeightShift a k : ℂ)

theorem shiftedWeight_eq_iff (lam : Fin d → ℂ) (a b : LowerRoot d →₀ ℕ) :
    shiftedWeight lam a = shiftedWeight lam b ↔ rootWeightShift a = rootWeightShift b := by
  constructor
  · intro h
    ext k
    have hk := congrFun h k
    simp only [shiftedWeight, add_right_inj] at hk
    exact_mod_cast hk
  · intro h
    funext k
    change lam k + (rootWeightShift a k : ℂ) = lam k + (rootWeightShift b k : ℂ)
    rw [congrFun h k]

/-- The exponent assignment records the exact joint weight of every lowering word. -/
theorem lowerWord_weight (R : Generators d H) (lam : Fin d → ℂ) (v : H → ℂ)
    (hweight : ∀ k, R.E k k *ᵥ v = lam k • v) (l : List (LowerRoot d)) (k : Fin d) :
    R.E k k *ᵥ (lowerWord R l *ᵥ v) =
      shiftedWeight lam (lowerExponent l) k • (lowerWord R l *ᵥ v) := by
  induction l generalizing k with
  | nil => simpa [lowerWord, lowerExponent_nil, shiftedWeight, rootWeightShift] using hweight k
  | cons r l ih =>
    have hw (j : Fin d) : R.E j j *ᵥ (lowerWord R l *ᵥ v) =
        shiftedWeight lam (lowerExponent l) j • (lowerWord R l *ᵥ v) :=
      ih j
    change R.E k k *ᵥ ((R.E r.val.2 r.val.1 * lowerWord R l) *ᵥ v) = _
    rw [← Matrix.mulVec_mulVec, R.raising_weight _ _ hw]
    have hcons : lowerWord R (r :: l) *ᵥ v =
        R.E r.val.2 r.val.1 *ᵥ (lowerWord R l *ᵥ v) := by
      simp only [lowerWord, List.map_cons, word_cons, loweringRoot, ← Matrix.mulVec_mulVec]
    rw [hcons]
    congr 1
    simp only [lowerExponent_cons, shiftedWeight, rootWeightShift_add, Pi.add_apply,
      rootWeightShift_single, Int.cast_add, Int.cast_sub]
    split_ifs <;> simp <;> ring

/-- Literal coordinate joint-weight space for an actual diagonal Cartan action. -/
def coordinateWeightSpace (wt : H → Fin d → ℂ) (target : Fin d → ℂ) : Submodule ℂ (H → ℂ) where
  carrier := {x | ∀ h, wt h ≠ target → x h = 0}
  zero_mem' := by simp
  add_mem' := by intro x y hx hy h hh; simp [hx h hh, hy h hh]
  smul_mem' := by intro c x hx h hh; simp [hx h hh]

def weightProjection (wt : H → Fin d → ℂ) (target : Fin d → ℂ) : (H → ℂ) →ₗ[ℂ] (H → ℂ) := by
  classical
  exact
    { toFun := fun x h => if wt h = target then x h else 0
      map_add' := by intro x y; ext h; split_ifs <;> simp_all
      map_smul' := by intro c x; ext h; split_ifs <;> simp_all }

theorem weightProjection_fix (wt : H → Fin d → ℂ) (target : Fin d → ℂ)
    (x : H → ℂ) (hx : x ∈ coordinateWeightSpace wt target) :
    weightProjection wt target x = x := by
  classical
  ext h
  change (if wt h = target then x h else 0) = x h
  split_ifs with hh
  · rfl
  · exact (hx h hh).symm

theorem eigenvector_mem_weightSpace (R : Generators d H) (wt : H → Fin d → ℂ)
    (hdiag : ∀ k, R.E k k = diagonal (fun h => wt h k))
    (target : Fin d → ℂ) (x : H → ℂ) (hx : ∀ k, R.E k k *ᵥ x = target k • x) :
    x ∈ coordinateWeightSpace wt target := by
  intro h hh
  obtain ⟨k, hk⟩ : ∃ k, wt h k ≠ target k := by
    by_contra hn
    push_neg at hn
    exact hh (funext hn)
  have he := congrFun (hx k) h
  rw [hdiag, Matrix.mulVec_diagonal] at he
  change wt h k * x h = target k * x h at he
  exact (mul_eq_zero.mp (show (wt h k - target k) * x h = 0 by
    rw [sub_mul, he, sub_self])).resolve_left (sub_ne_zero.mpr hk)

theorem weightProjection_other (wt : H → Fin d → ℂ) (target other : Fin d → ℂ)
    (hne : other ≠ target) (x : H → ℂ) (hx : x ∈ coordinateWeightSpace wt other) :
    weightProjection wt target x = 0 := by
  classical
  ext h
  change (if wt h = target then x h else 0) = 0
  split_ifs with hh
  · exact hx h (by simpa only [hh] using Ne.symm hne)
  · rfl

abbrev OrderedWordsAtWeight (a : LowerRoot d →₀ ℕ) :=
  {w : OrderedLoweringWord d // rootWeightShift (lowerExponent w.val) = rootWeightShift a}

def orderedWordsAtWeightEmbedding (a : LowerRoot d →₀ ℕ) :
    OrderedWordsAtWeight a ↪ (lowerWeightFiber a) where
  toFun w := ⟨lowerExponent w.val.val, (mem_lowerWeightFiber a _).mpr w.property⟩
  inj' := by
    intro a b h
    apply Subtype.ext
    apply lowerExponent_injective_on_ordered
    exact congrArg Subtype.val h

noncomputable instance orderedWordsAtWeightFintype (a : LowerRoot d →₀ ℕ) : Fintype (OrderedWordsAtWeight a) :=
  Fintype.ofInjective (orderedWordsAtWeightEmbedding a) (orderedWordsAtWeightEmbedding a).injective

def finiteWeightSpan (R : Generators d H) (v : H → ℂ) (a : LowerRoot d →₀ ℕ) :
    Submodule ℂ (H → ℂ) :=
  Submodule.span ℂ (Set.range (fun w : OrderedWordsAtWeight a => lowerWord R w.val.val *ᵥ v))

/-- Projecting the proved PBW span onto a weight leaves precisely its finite
root fiber; all discarded words have zero projection by their computed weights. -/
theorem projected_cyclic_mem_finiteWeightSpan
    (R : Generators d H) (wt : H → Fin d → ℂ)
    (hdiag : ∀ k, R.E k k = diagonal (fun h => wt h k))
    (lam : Fin d → ℂ) (v : H → ℂ)
    (hweight : ∀ k, R.E k k *ᵥ v = lam k • v)
    (hraise : ∀ i j, i < j → R.E i j *ᵥ v = 0)
    (a : LowerRoot d →₀ ℕ) (x : H → ℂ) (hx : x ∈ cyclicSpan R v) :
    weightProjection wt (shiftedWeight lam a) x ∈ finiteWeightSpan R v a := by
  rw [cyclicSpan_eq_orderedLoweringSpan R lam v hweight hraise] at hx
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨l, rfl⟩ := hx
    have hmem := eigenvector_mem_weightSpace R wt hdiag _ _ (lowerWord_weight R lam v hweight l.val)
    by_cases hl : rootWeightShift (lowerExponent l.val) = rootWeightShift a
    · have he := (shiftedWeight_eq_iff lam _ _).mpr hl
      rw [he] at hmem
      rw [weightProjection_fix wt _ _ hmem]
      exact Submodule.subset_span ⟨⟨l, hl⟩, rfl⟩
    · have he := mt (shiftedWeight_eq_iff lam _ _).mp hl
      rw [weightProjection_other wt _ _ he _ hmem]
      exact (finiteWeightSpan R v a).zero_mem
  | zero => simpa only [map_zero] using (finiteWeightSpan R v a).zero_mem
  | add x y hx hy hx' hy' => simpa only [map_add] using (finiteWeightSpan R v a).add_mem hx' hy'
  | smul c x hx hx' => simpa only [map_smul] using (finiteWeightSpan R v a).smul_mem c hx'

/-- The genuine PBW multiplicity upper bound, without a supplied count or
spanning hypothesis beyond actual highest-vector cyclicity. -/
theorem weightSpace_finrank_le_rootFiber
    (R : Generators d H) (wt : H → Fin d → ℂ)
    (hdiag : ∀ k, R.E k k = diagonal (fun h => wt h k))
    (lam : Fin d → ℂ) (v : H → ℂ)
    (hweight : ∀ k, R.E k k *ᵥ v = lam k • v)
    (hraise : ∀ i j, i < j → R.E i j *ᵥ v = 0)
    (hcyclic : cyclicSpan R v = ⊤) (a : LowerRoot d →₀ ℕ) :
    Module.finrank ℂ (coordinateWeightSpace wt (shiftedWeight lam a)) ≤ (lowerWeightFiber a).card := by
  have hle : coordinateWeightSpace wt (shiftedWeight lam a) ≤ finiteWeightSpan R v a := by
    intro x hx
    rw [← weightProjection_fix wt _ x hx]
    apply projected_cyclic_mem_finiteWeightSpan R wt hdiag lam v hweight hraise a x
    rw [hcyclic]
    trivial
  calc
    _ ≤ Module.finrank ℂ (finiteWeightSpan R v a) := Submodule.finrank_mono hle
    _ ≤ Fintype.card (OrderedWordsAtWeight a) := finrank_range_le_card _
    _ ≤ Fintype.card (lowerWeightFiber a) := Fintype.card_le_of_embedding (orderedWordsAtWeightEmbedding a)
    _ = _ := Fintype.card_coe _

/-- The upper bound also applies inside an ambient representation by taking
the actual intersection with the highest-vector cyclic span. -/
theorem cyclic_weightSpace_finrank_le_rootFiber
    (R : Generators d H) (wt : H → Fin d → ℂ)
    (hdiag : ∀ k, R.E k k = diagonal (fun h => wt h k))
    (lam : Fin d → ℂ) (v : H → ℂ)
    (hweight : ∀ k, R.E k k *ᵥ v = lam k • v)
    (hraise : ∀ i j, i < j → R.E i j *ᵥ v = 0)
    (a : LowerRoot d →₀ ℕ) :
    Module.finrank ℂ ↥(cyclicSpan R v ⊓ coordinateWeightSpace wt (shiftedWeight lam a) : Submodule ℂ (H → ℂ)) ≤
      (lowerWeightFiber a).card := by
  have hle : cyclicSpan R v ⊓ coordinateWeightSpace wt (shiftedWeight lam a) ≤ finiteWeightSpan R v a := by
    intro x hx
    rw [← weightProjection_fix wt _ x hx.2]
    exact projected_cyclic_mem_finiteWeightSpan R wt hdiag lam v hweight hraise a x hx.1
  calc
    _ ≤ Module.finrank ℂ (finiteWeightSpan R v a) := Submodule.finrank_mono hle
    _ ≤ Fintype.card (OrderedWordsAtWeight a) := finrank_range_le_card _
    _ ≤ Fintype.card (lowerWeightFiber a) := Fintype.card_le_of_embedding (orderedWordsAtWeightEmbedding a)
    _ = _ := Fintype.card_coe _

/-- Every nonzero coordinate of an actual highest-vector cyclic module has
a weight obtained by an actual positive-root assignment. This supplies the
root assignment instead of taking its existence as a representation premise. -/
theorem coordinate_weight_has_assignment
    (R : Generators d H) (wt : H → Fin d → ℂ)
    (hdiag : ∀ k, R.E k k = diagonal (fun h => wt h k))
    (lam : Fin d → ℂ) (v : H → ℂ)
    (hweight : ∀ k, R.E k k *ᵥ v = lam k • v)
    (hraise : ∀ i j, i < j → R.E i j *ᵥ v = 0)
    (x : H → ℂ) (hx : x ∈ cyclicSpan R v) (i : H) (hxi : x i ≠ 0) :
    ∃ a : LowerRoot d →₀ ℕ, wt i = shiftedWeight lam a := by
  classical
  by_contra hn
  push_neg at hn
  apply hxi
  clear hxi
  rw [cyclicSpan_eq_orderedLoweringSpan R lam v hweight hraise] at hx
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨l, rfl⟩ := hy
    exact eigenvector_mem_weightSpace R wt hdiag _ _
      (lowerWord_weight R lam v hweight l.val) i (hn (lowerExponent l.val))
  | zero => rfl
  | add y z hy hz hy' hz' => change y i + z i = 0; rw [hy', hz', add_zero]
  | smul c y hy hy' => simp [hy']

end FreeEntropy.LiePBW
