/-
Copyright (c) 2026 Free Entropy formalization contributors.
See LICENSE and NOTICE in the repository root for license and attribution.
-/

import FreeEntropy.GelfandTsetlin
import FreeEntropy.KostantCounting

/-!
# Gelfand–Tsetlin patterns as positive-root assignments

The root `(j,i)` carries the nonnegative vertical drop from row `i+1`
to row `i`, in column `j`. These drops reconstruct every entry from
the top row, so the resulting positive-root assignment is injective.
-/

noncomputable section

namespace FreeEntropy.GelfandTsetlin

open scoped BigOperators

/-- The vertical drop at the positive root `(j,i)`, zero off the root set. -/
def dropValue {d : ℕ} {μ : Fin d → ℤ} (P : Pattern μ) (p : ℕ × ℕ) : ℕ :=
  if hp : p ∈ Weyl.activeRoots d d then
    let h := Weyl.mem_activeRoots.mp hp
    (P.entry ⟨p.2 + 1, by omega⟩ ⟨p.1, by change p.1 < p.2 + 1; omega⟩ -
      P.entry ⟨p.2, by omega⟩ ⟨p.1, h.2.1⟩).toNat
  else 0

/-- The actual finite nonnegative root assignment of a GT pattern. -/
def drops {d : ℕ} {μ : Fin d → ℤ} (P : Pattern μ) : (ℕ × ℕ) →₀ ℕ :=
  Finsupp.onFinset (Weyl.activeRoots d d) (dropValue P) (by
    intro p hp
    by_contra h
    simp only [dropValue, dif_neg h] at hp
    exact hp rfl)

theorem drops_support {d : ℕ} {μ : Fin d → ℤ} (P : Pattern μ) :
    (drops P).support ⊆ Weyl.activeRoots d d := Finsupp.support_onFinset_subset

theorem drops_cast {d : ℕ} {μ : Fin d → ℤ} (P : Pattern μ)
    (i : Fin d) (j : Fin i.val) :
    ((drops P (j.val, i.val) : ℕ) : ℤ) =
      P.entry i.succ j.castSucc - P.entry i.castSucc j := by
  have hp : (j.val, i.val) ∈ Weyl.activeRoots d d := by
    rw [Weyl.mem_activeRoots]
    exact ⟨j.isLt.trans i.isLt, j.isLt, i.isLt⟩
  simp only [drops, Finsupp.onFinset_apply, dropValue, dif_pos hp]
  exact Int.toNat_of_nonneg (sub_nonneg.mpr (P.upper i j))

/-- The unweighted tail of one column of a root assignment. -/
def columnTail (d : ℕ) (c : (ℕ × ℕ) →₀ ℕ) (r j : ℕ) : ℤ :=
  ∑ k ∈ Finset.Ico r d, (c (j, k) : ℤ)

theorem columnTail_step (d : ℕ) (c : (ℕ × ℕ) →₀ ℕ)
    (r j : ℕ) (hr : r < d) :
    columnTail d c r j = c (j, r) + columnTail d c (r + 1) j := by
  exact Finset.sum_eq_sum_Ico_succ_bot hr (fun k => (c (j, k) : ℤ))

/-- Every entry is recovered from the top row by summing the vertical drops. -/
theorem reconstruct_entry {d : ℕ} {μ : Fin d → ℤ} (P : Pattern μ)
    (i : Fin (d + 1)) (j : Fin i.val) :
    P.entry i j = μ (column j) - columnTail d (drops P) i.val j.val := by
  have hrows : ∀ (r : ℕ) (hr : r ≤ d) (j : Fin r),
      P.entry ⟨r, Nat.lt_succ_of_le hr⟩ j =
      μ (column (i := ⟨r, Nat.lt_succ_of_le hr⟩) j) -
        columnTail d (drops P) r j.val := by
    intro r hr
    induction hr using Nat.decreasingInduction with
    | self =>
      intro j
      simpa [columnTail, column] using P.top j
    | @of_succ r hr ih =>
      intro j
      have hu := drops_cast P ⟨r, hr⟩ j
      have hs := columnTail_step d (drops P) r j.val hr
      have hi := ih j.castSucc
      change (drops P (j.val, r) : ℤ) =
        P.entry ⟨r + 1, _⟩ j.castSucc - P.entry ⟨r, _⟩ j at hu
      dsimp only [Fin.val_castSucc] at hi
      change P.entry ⟨r, _⟩ j = _
      have hc : column (i := (⟨r + 1, by omega⟩ : Fin (d + 1))) j.castSucc =
          column (i := (⟨r, by omega⟩ : Fin (d + 1))) j := Fin.ext rfl
      rw [hc] at hi
      omega
  exact hrows i.val (Nat.le_of_lt_succ i.isLt) j

/-- GT patterns inject into actual nonnegative positive-root assignments. -/
theorem drops_injective {d : ℕ} {μ : Fin d → ℤ} :
    Function.Injective (drops (μ := μ)) := by
  intro P Q h
  apply Pattern.ext
  funext i j
  rw [reconstruct_entry, reconstruct_entry, h]

theorem columnTail_nonneg (d : ℕ) (c : (ℕ × ℕ) →₀ ℕ) (r j : ℕ) :
    0 ≤ columnTail d c r j := Finset.sum_nonneg (fun _ _ => Nat.cast_nonneg _)

/-- Actual simple-root depth, with root `(j,i)` of height `i-j`. -/
def assignmentDepth (d : ℕ) (c : (ℕ × ℕ) →₀ ℕ) : ℕ :=
  KostantCounting.weightedDepth (Weyl.activeRoots d d) (fun p => p.2 - p.1) c

theorem columnTail_le_depth (d : ℕ) (c : (ℕ × ℕ) →₀ ℕ)
    (r j : ℕ) (hj : j < r) : columnTail d c r j ≤ assignmentDepth d c := by
  have hsub : (Finset.Ico r d).image (fun k => (j, k)) ⊆ Weyl.activeRoots d d := by
    intro p hp
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hp
    have hk' := Finset.mem_Ico.mp hk
    rw [Weyl.mem_activeRoots]
    omega
  have hsum : columnTail d c r j =
      ((∑ p ∈ (Finset.Ico r d).image (fun k => (j, k)), c p : ℕ) : ℤ) := by
    rw [Finset.sum_image]
    · simp only [columnTail, Nat.cast_sum]
    · intro a _ b _ h
      exact (Prod.mk.inj h).2
  rw [hsum]
  exact_mod_cast (Finset.sum_le_sum_of_subset hsub).trans
    (KostantCounting.ordinaryDegree_le_weightedDepth (Weyl.activeRoots d d) _
      (fun p hp => Nat.sub_pos_of_lt (Weyl.mem_activeRoots.mp hp).2.1) c)

/-- A lower bound on every adjacent top-row gap. -/
def HasGap {d : ℕ} (μ : Fin d → ℤ) (g : ℕ) : Prop :=
  ∀ (i : Fin d) (hi : i.val + 1 < d),
    (g : ℤ) ≤ μ i - μ ⟨i.val + 1, hi⟩

/-- Every root assignment of depth at most the adjacent gap reconstructs a GT pattern. -/
def fromDrops {d : ℕ} (μ : Fin d → ℤ) (c : (ℕ × ℕ) →₀ ℕ)
    {g : ℕ} (hgap : HasGap μ g) (hdepth : assignmentDepth d c ≤ g) : Pattern μ where
  entry i j := μ (column j) - columnTail d c i.val j.val
  top j := by simp [column, columnTail]
  upper i j := by
    have ht := columnTail_step d c i.val j.val i.isLt
    have hc : column (i := i.castSucc) j = column (i := i.succ) j.castSucc := Fin.ext rfl
    simp only [hc]
    change μ (column (i := i.succ) j.castSucc) - columnTail d c i.val j.val ≤
      μ (column (i := i.succ) j.castSucc) - columnTail d c (i.val + 1) j.val
    omega
  lower i j := by
    have hj : j.val + 1 < d := by omega
    have hg := hgap (column (i := i.castSucc) j) hj
    have hb := columnTail_le_depth d c i.val j.val j.isLt
    have hn := columnTail_nonneg d c (i.val + 1) (j.val + 1)
    have hd : (assignmentDepth d c : ℤ) ≤ g := by exact_mod_cast hdepth
    change μ ⟨j.val + 1, _⟩ - columnTail d c (i.val + 1) (j.val + 1) ≤
      μ (column (i := i.castSucc) j) - columnTail d c i.val j.val
    change (g : ℤ) ≤ μ (column (i := i.castSucc) j) - μ ⟨j.val + 1, hj⟩ at hg
    omega

theorem drops_fromDrops {d : ℕ} (μ : Fin d → ℤ) (c : (ℕ × ℕ) →₀ ℕ)
    {g : ℕ} (hgap : HasGap μ g) (hdepth : assignmentDepth d c ≤ g)
    (hsupport : c.support ⊆ Weyl.activeRoots d d) :
    drops (fromDrops μ c hgap hdepth) = c := by
  apply Finsupp.ext
  intro p
  by_cases hp : p ∈ Weyl.activeRoots d d
  · obtain ⟨hj, hji, hi⟩ := Weyl.mem_activeRoots.mp hp
    have hd := drops_cast (fromDrops μ c hgap hdepth) ⟨p.2, hi⟩ ⟨p.1, hji⟩
    have ht := columnTail_step d c p.2 p.1 hi
    change (drops (fromDrops μ c hgap hdepth) (p.1, p.2) : ℤ) =
      (μ ⟨p.1, hj⟩ - columnTail d c (p.2 + 1) p.1) -
      (μ ⟨p.1, hj⟩ - columnTail d c p.2 p.1) at hd
    exact_mod_cast (show (drops (fromDrops μ c hgap hdepth) p : ℤ) = c p by
      simpa only [Prod.eta] using (show
        (drops (fromDrops μ c hgap hdepth) (p.1, p.2) : ℤ) = c (p.1, p.2) by omega))
  · have hc : c p = 0 := Finsupp.notMem_support_iff.mp (fun h => hp (hsupport h))
    have hd : drops (fromDrops μ c hgap hdepth) p = 0 :=
      Finsupp.notMem_support_iff.mp (fun h => hp (drops_support _ h))
    rw [hd, hc]

theorem fromDrops_drops {d : ℕ} {μ : Fin d → ℤ} (P : Pattern μ)
    {g : ℕ} (hgap : HasGap μ g) (hdepth : assignmentDepth d (drops P) ≤ g) :
    fromDrops μ (drops P) hgap hdepth = P := by
  apply Pattern.ext
  funext i j
  exact (reconstruct_entry P i j).symm

/-- Column tails sum to the usual simple-root cut coefficient. -/
theorem sum_columnTail_eq_typeAOffset {d : ℕ} (c : (ℕ × ℕ) →₀ ℕ)
    (i : Fin (d + 1)) :
    (∑ j : Fin i.val, columnTail d c i.val j.val) =
      (KostantCounting.typeAOffset d c i.val : ℤ) := by
  have hrows (a : ℕ) :
      (∑ b ∈ Finset.Ico (a + 1) d, if a < i.val ∧ i.val ≤ b then c (a, b) else 0) =
      if a < i.val then ∑ b ∈ Finset.Ico i.val d, c (a, b) else 0 := by
    by_cases ha : a < i.val
    · simp only [ha, true_and, if_true]
      rw [← Finset.sum_filter]
      congr 1
      ext b
      simp only [Finset.mem_filter, Finset.mem_Ico]
      omega
    · simp [ha]
  have hfilter : (Finset.range d).filter (fun a => a < i.val) = Finset.range i.val := by
    ext a
    simp only [Finset.mem_filter, Finset.mem_range]
    have hi := i.isLt
    omega
  have hnat : KostantCounting.typeAOffset d c i.val =
      ∑ a ∈ Finset.range i.val, ∑ b ∈ Finset.Ico i.val d, c (a, b) := by
    unfold KostantCounting.typeAOffset
    rw [Weyl.sum_activeRoots]
    simp_rw [hrows]
    rw [← Finset.sum_filter, hfilter]
  rw [hnat]
  simp only [Nat.cast_sum, columnTail]
  exact Fin.sum_univ_eq_sum_range (fun a => ∑ b ∈ Finset.Ico i.val d, (c (a, b) : ℤ)) i.val

/-- Row sums of a GT pattern recover the simple-root offset from its root assignment. -/
theorem rowSum_eq_top_sub_cut {d : ℕ} {μ : Fin d → ℤ} (P : Pattern μ)
    (i : Fin (d + 1)) :
    rowSum P i = (∑ j : Fin i.val, μ (column j)) -
      (KostantCounting.typeAOffset d (drops P) i.val : ℤ) := by
  unfold rowSum
  simp_rw [reconstruct_entry]
  rw [Finset.sum_sub_distrib, sum_columnTail_eq_typeAOffset]

/-- Convert simple-root cut coefficients into standard-coordinate offsets. -/
def coordinateOffset (d : ℕ) (δ : ℕ → ℕ) : Fin d → ℤ :=
  fun i => (δ (i.val + 1) : ℤ) - δ i.val

/-- The root-assignment offset is exactly the offset of the GT weight. -/
theorem weight_eq_top_sub_offset {d : ℕ} {μ : Fin d → ℤ} (P : Pattern μ) :
    weight P = μ - coordinateOffset d (KostantCounting.typeAOffset d (drops P)) := by
  funext i
  simp only [weight, rowSum_eq_top_sub_cut, coordinateOffset, Pi.sub_apply]
  change ((∑ j : Fin (i.val + 1), μ (column (i := i.succ) j)) - _) -
      ((∑ j : Fin i.val, μ (column (i := i.castSucc) j)) - _) = _
  have hsum : (∑ j : Fin (i.val + 1), μ (column (i := i.succ) j)) =
      (∑ j : Fin i.val, μ (column (i := i.castSucc) j)) + μ i := by
    rw [Fin.sum_univ_castSucc]
    rfl
  rw [hsum]
  simp only [Fin.val_succ, Fin.val_castSucc]
  omega

/-- The finite set of actual GT patterns at a prescribed simple-root offset. -/
def CutPatterns {d : ℕ} (μ : Fin d → ℤ) (δ : ℕ → ℕ) :=
  {P : Pattern μ // KostantCounting.typeAOffset d (drops P) = δ}

instance {d : ℕ} (μ : Fin d → ℤ) (δ : ℕ → ℕ) : Fintype (CutPatterns μ δ) := by
  classical
  exact inferInstanceAs (Fintype {P : Pattern μ // KostantCounting.typeAOffset d (drops P) = δ})

def cutMultiplicity {d : ℕ} (μ : Fin d → ℤ) (δ : ℕ → ℕ) : ℕ :=
  Fintype.card (CutPatterns μ δ)

/-- The GT-to-root-assignment injection lands in the actual Kostant fiber. -/
def toKostantFiber {d : ℕ} {μ : Fin d → ℤ} {δ : ℕ → ℕ}
    (P : CutPatterns μ δ) : {c // c ∈ KostantCounting.kostantFiber d δ} :=
  ⟨drops P.val, (KostantCounting.mem_kostantFiber d δ _).mpr ⟨drops_support P.val, P.property⟩⟩

theorem toKostantFiber_injective {d : ℕ} {μ : Fin d → ℤ} {δ : ℕ → ℕ} :
    Function.Injective (toKostantFiber (μ := μ) (δ := δ)) := by
  intro P Q h
  apply Subtype.ext
  exact drops_injective (congrArg Subtype.val h)

/-- Actual GT multiplicities are bounded by actual Kostant partition counts. -/
theorem cutMultiplicity_le_kostantCount {d : ℕ} (μ : Fin d → ℤ) (δ : ℕ → ℕ) :
    cutMultiplicity μ δ ≤ KostantCounting.kostantCount d δ := by
  simpa only [cutMultiplicity, KostantCounting.kostantCount, Fintype.card_coe] using
    Fintype.card_le_of_injective (toKostantFiber (μ := μ) (δ := δ)) toKostantFiber_injective

/-- Every sufficiently shallow Kostant partition reconstructs a pattern in the same fiber. -/
def shallowFromKostantFiber {d : ℕ} (μ : Fin d → ℤ) (δ : ℕ → ℕ)
    {g : ℕ} (hgap : HasGap μ g) (hshallow : KostantCounting.offsetDepth d δ ≤ g)
    (c : {c // c ∈ KostantCounting.kostantFiber d δ}) : CutPatterns μ δ := by
  have hsupport := ((KostantCounting.mem_kostantFiber d δ c.val).mp c.property).1
  have hoffset := ((KostantCounting.mem_kostantFiber d δ c.val).mp c.property).2
  have hd : assignmentDepth d c.val ≤ g := by
    rw [assignmentDepth, ← KostantCounting.offsetDepth_typeAOffset, hoffset]
    exact hshallow
  exact ⟨fromDrops μ c.val hgap hd, by rw [drops_fromDrops _ _ _ _ hsupport, hoffset]⟩

/-- In the shallow range, the GT-to-Kostant injection is a bijection. -/
theorem toKostantFiber_surjective_of_shallow {d : ℕ} (μ : Fin d → ℤ) (δ : ℕ → ℕ)
    {g : ℕ} (hgap : HasGap μ g) (hshallow : KostantCounting.offsetDepth d δ ≤ g) :
    Function.Surjective (toKostantFiber (μ := μ) (δ := δ)) := by
  intro c
  refine ⟨shallowFromKostantFiber μ δ hgap hshallow c, ?_⟩
  apply Subtype.ext
  dsimp only [toKostantFiber, shallowFromKostantFiber]
  apply drops_fromDrops
  exact ((KostantCounting.mem_kostantFiber d δ c.val).mp c.property).1

/-- The exact shallow-weight equality of GT multiplicities and Kostant counts. -/
theorem cutMultiplicity_eq_kostantCount_of_shallow {d : ℕ}
    (μ : Fin d → ℤ) (δ : ℕ → ℕ) {g : ℕ}
    (hgap : HasGap μ g) (hshallow : KostantCounting.offsetDepth d δ ≤ g) :
    cutMultiplicity μ δ = KostantCounting.kostantCount d δ := by
  simpa only [cutMultiplicity, KostantCounting.kostantCount, Fintype.card_coe] using
    Fintype.card_of_bijective
      ⟨toKostantFiber_injective, toKostantFiber_surjective_of_shallow μ δ hgap hshallow⟩

/-- Simple-root offsets have zero coefficients at the two boundary cuts and beyond. -/
def ValidCuts (d : ℕ) (δ : ℕ → ℕ) : Prop :=
  δ 0 = 0 ∧ ∀ k, d ≤ k → δ k = 0

theorem typeAOffset_valid (d : ℕ) (c : (ℕ × ℕ) →₀ ℕ) :
    ValidCuts d (KostantCounting.typeAOffset d c) := by
  constructor
  · simp [KostantCounting.typeAOffset]
  · intro k hk
    apply Finset.sum_eq_zero
    intro p hp
    have hp' := Weyl.mem_activeRoots.mp hp
    exact if_neg (by omega)

/-- Standard weight coordinates uniquely determine valid simple-root cut coefficients. -/
theorem coordinateOffset_injective {d : ℕ} {δ ε : ℕ → ℕ}
    (hδ : ValidCuts d δ) (hε : ValidCuts d ε)
    (h : coordinateOffset d δ = coordinateOffset d ε) : δ = ε := by
  have hle : ∀ k, k ≤ d → δ k = ε k := by
    intro k
    induction k with
    | zero => intro _; exact hδ.1.trans hε.1.symm
    | succ k ih =>
      intro hk
      have hk' : k < d := by omega
      have hi := ih (by omega)
      have hc := congrFun h ⟨k, hk'⟩
      change (δ (k + 1) : ℤ) - δ k = (ε (k + 1) : ℤ) - ε k at hc
      omega
  funext k
  by_cases hk : k ≤ d
  · exact hle k hk
  · exact (hδ.2 k (by omega)).trans (hε.2 k (by omega)).symm

/-- The drop fiber condition is exactly the usual GT weight condition. -/
theorem cut_eq_iff_weight_eq {d : ℕ} {μ : Fin d → ℤ} (P : Pattern μ)
    {δ : ℕ → ℕ} (hδ : ValidCuts d δ) :
    KostantCounting.typeAOffset d (drops P) = δ ↔
      weight P = μ - coordinateOffset d δ := by
  constructor
  · intro h
    rw [weight_eq_top_sub_offset, h]
  · intro h
    apply coordinateOffset_injective (typeAOffset_valid d (drops P)) hδ
    funext i
    have hw := congrFun (weight_eq_top_sub_offset P) i
    rw [h] at hw
    simp only [Pi.sub_apply] at hw
    omega

/-- An explicit equivalence between cut-indexed and ordinary weight-indexed GT patterns. -/
def cutOffsetEquiv {d : ℕ} (μ : Fin d → ℤ) (δ : ℕ → ℕ) (hδ : ValidCuts d δ) :
    CutPatterns μ δ ≃ OffsetPatterns μ (coordinateOffset d δ) where
  toFun P := ⟨P.val, (cut_eq_iff_weight_eq P.val hδ).mp P.property⟩
  invFun P := ⟨P.val, (cut_eq_iff_weight_eq P.val hδ).mpr P.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem cutMultiplicity_eq_multiplicity {d : ℕ} (μ : Fin d → ℤ)
    (δ : ℕ → ℕ) (hδ : ValidCuts d δ) :
    cutMultiplicity μ δ = multiplicity μ (coordinateOffset d δ) :=
  Fintype.card_congr (cutOffsetEquiv μ δ hδ)

/-- The actual ordinary GT weight multiplicity satisfies the Kostant partition upper bound. -/
theorem multiplicity_le_kostantCount {d : ℕ} (μ : Fin d → ℤ)
    (δ : ℕ → ℕ) (hδ : ValidCuts d δ) :
    multiplicity μ (coordinateOffset d δ) ≤ KostantCounting.kostantCount d δ := by
  rw [← cutMultiplicity_eq_multiplicity μ δ hδ]
  exact cutMultiplicity_le_kostantCount μ δ

/-- The paper's shallow multiplicity equality, for actual GT counts at actual weights. -/
theorem multiplicity_eq_kostantCount_of_shallow {d : ℕ}
    (μ : Fin d → ℤ) (δ : ℕ → ℕ) {g : ℕ}
    (hδ : ValidCuts d δ) (hgap : HasGap μ g)
    (hshallow : KostantCounting.offsetDepth d δ ≤ g) :
    multiplicity μ (coordinateOffset d δ) = KostantCounting.kostantCount d δ := by
  rw [← cutMultiplicity_eq_multiplicity μ δ hδ]
  exact cutMultiplicity_eq_kostantCount_of_shallow μ δ hgap hshallow

theorem hasGap_add_dominant {d : ℕ} {μ ω : Fin d → ℤ} {g : ℕ}
    (hgap : HasGap μ g) (hω : Dominant ω) : HasGap (μ + ω) g := by
  intro i hi
  have hg := hgap i hi
  have hw : ω ⟨i.val + 1, hi⟩ ≤ ω i := hω (by change i.val ≤ i.val + 1; omega)
  simp only [Pi.add_apply]
  omega

/-- Adding a dominant highest weight preserves every multiplicity in the shallow range. -/
theorem multiplicity_eq_add_of_shallow {d : ℕ} {μ ω : Fin d → ℤ}
    (δ : ℕ → ℕ) {g : ℕ} (hδ : ValidCuts d δ) (hω : Dominant ω)
    (hgap : HasGap μ g) (hshallow : KostantCounting.offsetDepth d δ ≤ g) :
    multiplicity μ (coordinateOffset d δ) =
      multiplicity (μ + ω) (coordinateOffset d δ) := by
  rw [multiplicity_eq_kostantCount_of_shallow μ δ hδ hgap hshallow,
    multiplicity_eq_kostantCount_of_shallow (μ + ω) δ hδ
      (hasGap_add_dominant hgap hω) hshallow]

theorem dominant_hasGap_zero {d : ℕ} {μ : Fin d → ℤ} (hμ : Dominant μ) :
    HasGap μ 0 := by
  intro i hi
  apply sub_nonneg.mpr
  exact hμ (by change i.val ≤ i.val + 1; omega)

/-- The actual column-constant highest-weight GT pattern. -/
def highestPattern {d : ℕ} (μ : Fin d → ℤ) (hμ : Dominant μ) : Pattern μ :=
  fromDrops μ 0 (dominant_hasGap_zero hμ)
    (by simp [assignmentDepth, KostantCounting.weightedDepth])

theorem highestPattern_entry {d : ℕ} (μ : Fin d → ℤ) (hμ : Dominant μ)
    (i : Fin (d + 1)) (j : Fin i.val) :
    (highestPattern μ hμ).entry i j = μ (column j) := by
  simp [highestPattern, fromDrops, columnTail]

theorem drops_highestPattern {d : ℕ} (μ : Fin d → ℤ) (hμ : Dominant μ) :
    drops (highestPattern μ hμ) = 0 := by
  apply drops_fromDrops
  simp

theorem weight_highestPattern {d : ℕ} (μ : Fin d → ℤ) (hμ : Dominant μ) :
    weight (highestPattern μ hμ) = μ := by
  rw [weight_eq_top_sub_offset, drops_highestPattern]
  have hz : coordinateOffset d (KostantCounting.typeAOffset d 0) = 0 := by
    funext i
    simp [coordinateOffset, KostantCounting.typeAOffset]
  rw [hz, sub_zero]

end FreeEntropy.GelfandTsetlin
