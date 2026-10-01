/-
Copyright (c) 2026 Free Entropy formalization contributors.
See LICENSE and NOTICE in the repository root for license and attribution.
-/

import FreeEntropy.RaisingKernel
import FreeEntropy.CoordinateWeightSpace

/-! The complete depth layer of an actual cyclic highest-weight module has
the positive-root partition bound. This derives the coefficient envelope
used by the normalized-state mean-depth estimate directly from PBW. -/
noncomputable section
open Matrix
open scoped BigOperators
namespace FreeEntropy.CartanLieCloning
open LieMatrixCasimir LiePBW ExteriorRepresentation CasimirWeights
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
variable {d : ℕ} {A : Type*} [Fintype A] [DecidableEq A]

theorem CyclicWeightModel.lowerWord_depth (M : CyclicWeightModel d A)
    (l : List (LowerRoot d)) (b : A) (hb : (lowerWord M.generators l *ᵥ M.highestVector) b ≠ 0) :
    rootDepth (lowerExponent l) = M.basisDepth b := by
  have he (k : Fin d) : M.weight b k - M.row k = (rootWeightShift (lowerExponent l) k : ℝ) := by
    have h := congrFun (lowerWord_weight M.generators (fun k => (M.row k : ℂ))
      M.highestVector M.vector_weight l k) b
    rw [M.diagonal] at h
    simp only [WeightSectors.weightDiagonal, Matrix.mulVec_diagonal, Pi.smul_apply, smul_eq_mul] at h
    have hc := mul_right_cancel₀ hb h
    have hr := congrArg Complex.re hc
    simp only [shiftedWeight, Complex.ofReal_re, Complex.add_re, Complex.intCast_re] at hr
    linarith
  have hr : (rootDepth (lowerExponent l) : ℝ) =
      ∑ k : Fin d, (k.val : ℝ) * (rootWeightShift (lowerExponent l) k : ℝ) := by
    exact_mod_cast rootDepth_eq_weightShift (lowerExponent l)
  rw [← Nat.cast_inj (R := ℝ), M.depth_eq_energy]
  rw [hr]
  simp_rw [← he, mul_sub, Finset.sum_sub_distrib]

abbrev OrderedWordsAtDepth (d t : ℕ) :=
  {l : OrderedLoweringWord d // rootDepth (lowerExponent l.val) = t}

def orderedDepthEmbedding (t : ℕ) : OrderedWordsAtDepth d t ↪ (lowerAssignmentsAtDepth (d := d) t) where
  toFun l := ⟨lowerExponent l.val.val, (mem_lowerAssignmentsAtDepth _ _).mpr l.property⟩
  inj' := by
    intro l m h
    apply Subtype.ext
    exact lowerExponent_injective_on_ordered (congrArg Subtype.val h)

noncomputable instance orderedWordsAtDepthFintype (t : ℕ) : Fintype (OrderedWordsAtDepth d t) :=
  Fintype.ofInjective (orderedDepthEmbedding t) (orderedDepthEmbedding t).injective

def CyclicWeightModel.depthProjection (M : CyclicWeightModel d A) (t : ℕ) : (A → ℂ) →ₗ[ℂ] (A → ℂ) := by
  classical
  exact
    { toFun := fun x a => if M.basisDepth a = t then x a else 0
      map_add' := by intros; ext a; split_ifs <;> simp_all
      map_smul' := by intros; ext a; split_ifs <;> simp_all }

def CyclicWeightModel.depthSpace (M : CyclicWeightModel d A) (t : ℕ) : Submodule ℂ (A → ℂ) :=
  coordinateWeightSpace (d := 1) (fun a _ => (M.basisDepth a : ℂ)) (fun _ => (t : ℂ))

theorem CyclicWeightModel.depthProjection_fix (M : CyclicWeightModel d A) (t : ℕ)
    (x : A → ℂ) (hx : x ∈ M.depthSpace t) : M.depthProjection t x = x := by
  classical
  ext a
  change (if M.basisDepth a = t then x a else 0) = x a
  split_ifs with ha
  · rfl
  · apply (hx a _).symm
    intro he
    apply ha
    have hh := congrFun he (0 : Fin 1)
    change (M.basisDepth a : ℂ) = (t : ℂ) at hh
    exact_mod_cast hh

theorem CyclicWeightModel.depthProjection_lowerWord (M : CyclicWeightModel d A) (t : ℕ)
    (l : List (LowerRoot d)) :
    M.depthProjection t (lowerWord M.generators l *ᵥ M.highestVector) =
      if rootDepth (lowerExponent l) = t then lowerWord M.generators l *ᵥ M.highestVector else 0 := by
  classical
  ext a
  by_cases hz : (lowerWord M.generators l *ᵥ M.highestVector) a = 0
  · by_cases ht : rootDepth (lowerExponent l) = t <;> simp [depthProjection, ht, hz]
  · have hd := M.lowerWord_depth l a hz
    by_cases ht : M.basisDepth a = t <;> simp [depthProjection, hd, ht]

def CyclicWeightModel.finiteDepthSpan (M : CyclicWeightModel d A) (t : ℕ) : Submodule ℂ (A → ℂ) :=
  Submodule.span ℂ (Set.range (fun l : OrderedWordsAtDepth d t => lowerWord M.generators l.val.val *ᵥ M.highestVector))

theorem CyclicWeightModel.projected_mem_finiteDepthSpan (M : CyclicWeightModel d A) (t : ℕ) (x : A → ℂ) :
    M.depthProjection t x ∈ M.finiteDepthSpan t := by
  classical
  have hx : x ∈ cyclicSpan M.generators M.highestVector := by rw [M.vector_cyclic]; trivial
  rw [cyclicSpan_eq_orderedLoweringSpan M.generators (fun k => (M.row k : ℂ))
    M.highestVector M.vector_weight M.vector_raise] at hx
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨l, rfl⟩ := hx
    rw [M.depthProjection_lowerWord]
    split_ifs with hl
    · exact Submodule.subset_span ⟨⟨l, hl⟩, rfl⟩
    · exact Submodule.zero_mem _
  | zero => simpa only [map_zero] using (M.finiteDepthSpan t).zero_mem
  | add x y hx hy hx' hy' => simpa only [map_add] using (M.finiteDepthSpan t).add_mem hx' hy'
  | smul c x hx hx' => simpa only [map_smul] using (M.finiteDepthSpan t).smul_mem c hx'

theorem CyclicWeightModel.depthSpace_finrank (M : CyclicWeightModel d A) (t : ℕ) :
    Module.finrank ℂ (M.depthSpace t) = Fintype.card {a : A // M.basisDepth a = t} := by
  classical
  rw [depthSpace, coordinateWeightSpace_finrank]
  apply Fintype.card_congr
  apply Equiv.subtypeEquivRight
  intro a
  constructor
  · intro h
    exact_mod_cast congrFun h (0 : Fin 1)
  · intro h
    simp only [h]

/-- Actual total weight multiplicity at fixed depth, with no count hypotheses. -/
theorem CyclicWeightModel.depthMultiplicity_le (M : CyclicWeightModel d A) (hd : 2 ≤ d) (t : ℕ) :
    Fintype.card {a : A // M.basisDepth a = t} ≤
      (t + d.choose 2 - 1).choose (d.choose 2 - 1) := by
  have hle : M.depthSpace t ≤ M.finiteDepthSpan t := by
    intro x hx
    rw [← M.depthProjection_fix t x hx]
    exact M.projected_mem_finiteDepthSpan t x
  calc
    _ = Module.finrank ℂ (M.depthSpace t) := (M.depthSpace_finrank t).symm
    _ ≤ Module.finrank ℂ (M.finiteDepthSpan t) := Submodule.finrank_mono hle
    _ ≤ Fintype.card (OrderedWordsAtDepth d t) := finrank_range_le_card _
    _ ≤ Fintype.card (lowerAssignmentsAtDepth (d := d) t) := Fintype.card_le_of_embedding (orderedDepthEmbedding t)
    _ = (lowerAssignmentsAtDepth (d := d) t).card := Fintype.card_coe _
    _ ≤ _ := card_lowerAssignmentsAtDepth_le hd t

/-- The actual type-A simple-root coordinates are unique. -/
theorem offset_injective : Function.Injective (offset (d := d)) := by
  intro c e h
  funext j
  have hp := congrArg (fun x : Fin d → ℝ => ∑ k : Fin d with k.val ≤ j.val, x k) h
  simp only [CasimirDecomposition.prefix_offset] at hp
  exact_mod_cast hp

theorem CyclicWeightModel.weightCoeff_eq_of_weight (M : CyclicWeightModel d A)
    (a : A) (delta : Fin (d - 1) → ℕ) (h : M.weight a = M.row - offset delta) :
    M.weightCoeff a = delta := by
  apply offset_injective
  rw [← M.weight_cone a, h]
  abel

/-- Summing literal weight multiplicities over any finite collection of
simple-root offsets retains the same binomial depth bound. -/
theorem CyclicWeightModel.offsetMultiplicity_depth_le (M : CyclicWeightModel d A)
    (hd : 2 ≤ d) (s : Finset (Fin (d - 1) → ℕ)) (t : ℕ) :
    (∑ delta ∈ s with depth delta = t,
      weightMultiplicity M.weight (M.row - offset delta)) ≤
      (t + d.choose 2 - 1).choose (d.choose 2 - 1) := by
  classical
  let F := fun delta : Fin (d - 1) → ℕ => Finset.univ.filter (fun a : A => M.weight a = M.row - offset delta)
  have hj : (↑(s.filter (fun delta => depth delta = t)) : Set (Fin (d - 1) → ℕ)).PairwiseDisjoint F := by
    intro c hc e he hce
    apply Finset.disjoint_left.mpr
    intro a hac hae
    have hca := M.weightCoeff_eq_of_weight a c (Finset.mem_filter.mp hac).2
    have hea := M.weightCoeff_eq_of_weight a e (Finset.mem_filter.mp hae).2
    exact hce (hca.symm.trans hea)
  have hle : (s.filter (fun delta => depth delta = t)).biUnion F ⊆
      Finset.univ.filter (fun a => M.basisDepth a = t) := by
    intro a ha
    obtain ⟨delta, hdelta, hadelta⟩ := Finset.mem_biUnion.mp ha
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    have he := M.weightCoeff_eq_of_weight a delta (Finset.mem_filter.mp hadelta).2
    change depth (M.weightCoeff a) = t
    rw [he]
    exact (Finset.mem_filter.mp hdelta).2
  change (∑ delta ∈ s.filter (fun delta => depth delta = t), (F delta).card) ≤ _
  rw [← Finset.card_biUnion hj]
  apply (Finset.card_le_card hle).trans
  simpa only [Fintype.card_subtype] using M.depthMultiplicity_le hd t

end FreeEntropy.CartanLieCloning
