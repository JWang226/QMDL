/-
Copyright (c) 2026 Free Entropy formalization contributors.
See LICENSE and NOTICE in the repository root for license and attribution.
-/

import FreeEntropy.ExteriorCommutant
import FreeEntropy.ExteriorLowerMinors

/-! Distinct exterior columns encode genuine lower-root monomials. Finite
fiber-cardinality inequalities construct the allocation; no injection is assumed. -/
noncomputable section
open Matrix
open scoped BigOperators
namespace FreeEntropy.ExteriorRepresentation
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
set_option linter.unusedSectionVars false

section Allocation
variable {X Y : Type*} [Fintype X] [Fintype Y]

def cardEmbedding (h : Fintype.card X ≤ Fintype.card Y) : X ↪ Y :=
  (Fintype.equivFin X).toEmbedding.trans
    ((Fin.castLEEmb h).trans (Fintype.equivFin Y).symm.toEmbedding)

def fiberCardEmbedding (f : X → ℕ) (g : Y → ℕ)
    (h : ∀ k, Fintype.card {x // f x = k} ≤ Fintype.card {y // g y = k}) : X ↪ Y :=
  (Equiv.sigmaFiberEquiv f).symm.toEmbedding.trans
    ((Function.Embedding.sigmaMap (Function.Embedding.refl ℕ)
      (fun k => cardEmbedding (h k))).trans (Equiv.sigmaFiberEquiv g).toEmbedding)

theorem fiberCardEmbedding_preserves (f : X → ℕ) (g : Y → ℕ)
    (h : ∀ k, Fintype.card {x // f x = k} ≤ Fintype.card {y // g y = k}) (x : X) :
    g (fiberCardEmbedding f g h x) = f x :=
  (cardEmbedding (h (f x)) (⟨x, rfl⟩ : {y : X // f y = f x})).property

end Allocation

variable {d : ℕ}
@[simp] theorem indexCast_val {k l : ℕ} (h : k = l) (s : Index d k) :
    (indexCast h s).val = s.val := by subst l; rfl

abbrev LowerRoot (d : ℕ) := {p : Fin d × Fin d // p.1 < p.2}
abbrev RootCopies (a : LowerRoot d →₀ ℕ) := Σ r : LowerRoot d, Fin (a r)

def rootCopyHeight (a : LowerRoot d →₀ ℕ) (x : RootCopies a) := x.1.val.1.val + 1

theorem rootCopies_card (a : LowerRoot d →₀ ℕ) : Fintype.card (RootCopies a) = ∑ r, a r := by
  simp [RootCopies, Fintype.card_sigma]

/-- The exact minor for an unmodified highest exterior factor is one. -/
theorem lowerUnitriangular_first_minor (L : Matrix (Fin d) (Fin d) ℂ)
    (hupper : ∀ i j, i < j → L i j = 0) (hdiag : ∀ i, L i i = 1)
    (k : ℕ) (hk : k ≤ d) : exteriorMatrix k L (first hk) (first hk) = 1 := by
  rw [exteriorMatrix_apply]
  let M := L.submatrix (enumerate (first hk)) (enumerate (first hk))
  have hm : M.BlockTriangular OrderDual.toDual := by
    intro i j hij
    change L (enumerate (first hk) i) (enumerate (first hk) j) = 0
    rw [enumerate_first, enumerate_first]
    exact hupper _ _ hij
  change M.det = 1
  rw [Matrix.det_of_lowerTriangular M hm]
  apply Finset.prod_eq_one
  intro i _
  exact hdiag _

variable (mu : Fin d → ℕ) (a : LowerRoot d →₀ ℕ)

/-- Allocate each root occurrence to a different exterior factor of the
required height, using only actual fiber cardinalities. -/
def rootColumnEmbedding
    (hcapacity : ∀ k, Fintype.card {x : RootCopies a // rootCopyHeight a x = k} ≤ heightFiber mu k) :
    RootCopies a ↪ Column mu :=
  fiberCardEmbedding (rootCopyHeight a) (columnHeight mu)
    (fun k => by simpa only [Fintype.card_subtype, heightFiber] using hcapacity k)

theorem rootColumnEmbedding_height
    (hcapacity : ∀ k, Fintype.card {x : RootCopies a // rootCopyHeight a x = k} ≤ heightFiber mu k)
    (x : RootCopies a) :
    columnHeight mu (rootColumnEmbedding mu a hcapacity x) = x.1.val.1.val + 1 :=
  fiberCardEmbedding_preserves _ _ _ x

/-- The selected tensor-basis coordinate, built from allocated replacement subsets. -/
def monomialBasis
    (hcapacity : ∀ k, Fintype.card {x : RootCopies a // rootCopyHeight a x = k} ≤ heightFiber mu k) :
    AmbientIndex mu := fun c =>
  if hc : ∃ x : RootCopies a, rootColumnEmbedding mu a hcapacity x = c then
    let x := Classical.choose hc
    indexCast (by rw [← Classical.choose_spec hc, rootColumnEmbedding_height])
      (replacementSubset x.1.val.2 x.1.val.1 (le_of_lt x.1.property))
  else first (columnHeight_le mu c)

theorem monomialBasis_at
    (hcapacity : ∀ k, Fintype.card {x : RootCopies a // rootCopyHeight a x = k} ≤ heightFiber mu k)
    (x : RootCopies a) :
    monomialBasis mu a hcapacity (rootColumnEmbedding mu a hcapacity x) =
      indexCast (rootColumnEmbedding_height mu a hcapacity x).symm
        (replacementSubset x.1.val.2 x.1.val.1 (le_of_lt x.1.property)) := by
  have hc : ∃ y : RootCopies a, rootColumnEmbedding mu a hcapacity y =
      rootColumnEmbedding mu a hcapacity x := ⟨x, rfl⟩
  have he : Classical.choose hc = x :=
    (rootColumnEmbedding mu a hcapacity).injective (Classical.choose_spec hc)
  simp only [monomialBasis, dif_pos hc]
  apply Subtype.ext
  simp only [indexCast_val]
  exact congrArg (fun y : RootCopies a =>
    (replacementSubset y.1.val.2 y.1.val.1 (le_of_lt y.1.property)).val) he

theorem monomialBasis_off
    (hcapacity : ∀ k, Fintype.card {x : RootCopies a // rootCopyHeight a x = k} ≤ heightFiber mu k)
    (c : Column mu) (hc : c ∉ Set.range (rootColumnEmbedding mu a hcapacity)) :
    monomialBasis mu a hcapacity c = first (columnHeight_le mu c) := by
  have hn : ¬∃ x : RootCopies a, rootColumnEmbedding mu a hcapacity x = c := hc
  simp only [monomialBasis, dif_neg hn]

/-- The selected coordinate of the actual polynomial orbit is exactly the
root monomial, with no unknown scalar or lower-order terms. -/
theorem monomialBasis_coefficient
    (hcapacity : ∀ k, Fintype.card {x : RootCopies a // rootCopyHeight a x = k} ≤ heightFiber mu k)
    (L : Matrix (Fin d) (Fin d) ℂ)
    (hupper : ∀ i j, i < j → L i j = 0) (hdiag : ∀ i, L i i = 1) :
    tensorMatrix (columnHeight mu) L (monomialBasis mu a hcapacity) (highestBasisIndex mu) =
      ∏ r : LowerRoot d, L r.val.2 r.val.1 ^ a r := by
  change (∏ c : Column mu, exteriorMatrix (columnHeight mu c) L
    (monomialBasis mu a hcapacity c) (first (columnHeight_le mu c))) = _
  have hi (x : RootCopies a) :
      exteriorMatrix (columnHeight mu (rootColumnEmbedding mu a hcapacity x)) L
        (monomialBasis mu a hcapacity (rootColumnEmbedding mu a hcapacity x))
        (first (columnHeight_le mu _)) = L x.1.val.2 x.1.val.1 := by
    rw [monomialBasis_at]
    rw [← indexCast_first (rootColumnEmbedding_height mu a hcapacity x).symm
      (Nat.succ_le_of_lt x.1.val.1.isLt) (columnHeight_le mu _)]
    rw [exteriorMatrix_indexCast]
    exact lowerUnitriangular_replacement_minor L hupper hdiag _ _ (le_of_lt x.1.property)
  have hp := Fintype.prod_of_injective (rootColumnEmbedding mu a hcapacity)
    (rootColumnEmbedding mu a hcapacity).injective
    (fun x : RootCopies a => L x.1.val.2 x.1.val.1)
    (fun c : Column mu => exteriorMatrix (columnHeight mu c) L
      (monomialBasis mu a hcapacity c) (first (columnHeight_le mu c)))
    (fun c hc => by
      dsimp only
      rw [monomialBasis_off mu a hcapacity c hc]
      exact lowerUnitriangular_first_minor L hupper hdiag _ _) (fun x => (hi x).symm)
  rw [← hp, Fintype.prod_sigma]
  simp

/-- The positive-root height of an actual finite root assignment. -/
def rootDepth : ℕ := ∑ r : LowerRoot d, (r.val.2.val - r.val.1.val) * a r

theorem rootCopies_card_le_depth : Fintype.card (RootCopies a) ≤ rootDepth a := by
  rw [rootCopies_card]
  apply Finset.sum_le_sum
  intro r _
  have h : 1 ≤ r.val.2.val - r.val.1.val := by have := r.property; change r.val.1.val < r.val.2.val at this; omega
  simpa using Nat.mul_le_mul_right (a r) h

theorem heightFiber_adjacent (hmu : Antitone mu) (j : Fin d) (hj : j.val + 1 < d) :
    heightFiber mu (j.val + 1) + mu ⟨j.val + 1, hj⟩ = mu j := by
  have h := heightFiber_succ_add mu j.val
  rw [heightTail_eq mu hmu, heightTail_eq mu hmu] at h
  simpa only [rowAt, dif_pos hj, dif_pos j.isLt] using h

/-- The shallow-depth bound alone provides enough distinct exterior columns
for every positive-root assignment, by the actual adjacent highest-weight gaps. -/
theorem shallow_root_capacity (hmu : Antitone mu) (g : ℕ)
    (hgap : ∀ j : Fin d, ∀ hj : j.val + 1 < d, g + mu ⟨j.val + 1, hj⟩ ≤ mu j)
    (hdepth : rootDepth a ≤ g) (k : ℕ) :
    Fintype.card {x : RootCopies a // rootCopyHeight a x = k} ≤ heightFiber mu k := by
  classical
  by_cases hn : Nonempty {x : RootCopies a // rootCopyHeight a x = k}
  · obtain ⟨⟨x, hx⟩⟩ := hn
    have hj : x.1.val.1.val + 1 < d := by
      have hr := x.1.property
      have hi := x.1.val.2.isLt
      change x.1.val.1.val < x.1.val.2.val at hr
      omega
    have hg := hgap x.1.val.1 hj
    have hf := heightFiber_adjacent mu hmu x.1.val.1 hj
    have hc := Fintype.card_subtype_le (fun x : RootCopies a => rootCopyHeight a x = k)
    have hd := rootCopies_card_le_depth a
    change x.1.val.1.val + 1 = k at hx
    have hfg : g ≤ heightFiber mu (x.1.val.1.val + 1) := by omega
    rw [hx] at hfg
    omega
  · haveI : IsEmpty {x : RootCopies a // rootCopyHeight a x = k} := not_nonempty_iff.mp hn
    simp

def shallowMonomialBasis (hmu : Antitone mu) (g : ℕ)
    (hgap : ∀ j : Fin d, ∀ hj : j.val + 1 < d, g + mu ⟨j.val + 1, hj⟩ ≤ mu j)
    (hdepth : rootDepth a ≤ g) : AmbientIndex mu :=
  monomialBasis mu a (shallow_root_capacity mu a hmu g hgap hdepth)

/-- A literal lower unitriangular matrix with one independent complex variable
for every positive root. -/
def lowerRootMatrix (x : LowerRoot d → ℂ) : Matrix (Fin d) (Fin d) ℂ :=
  fun i j => if h : j < i then x ⟨(j, i), h⟩ else if i = j then 1 else 0

theorem lowerRootMatrix_upper (x : LowerRoot d → ℂ) (i j : Fin d) (hij : i < j) :
    lowerRootMatrix x i j = 0 := by
  simp [lowerRootMatrix, not_lt_of_ge hij.le, ne_of_lt hij]

theorem lowerRootMatrix_diagonal (x : LowerRoot d → ℂ) (i : Fin d) :
    lowerRootMatrix x i i = 1 := by simp [lowerRootMatrix]

theorem lowerRootMatrix_root (x : LowerRoot d → ℂ) (r : LowerRoot d) :
    lowerRootMatrix x r.val.2 r.val.1 = x r := by simp [lowerRootMatrix, r.property]

/-- Exact monomial coordinates, with the allocation hypothesis discharged
by depth and adjacent row gaps. -/
theorem shallowMonomialBasis_coefficient (hmu : Antitone mu) (g : ℕ)
    (hgap : ∀ j : Fin d, ∀ hj : j.val + 1 < d, g + mu ⟨j.val + 1, hj⟩ ≤ mu j)
    (hdepth : rootDepth a ≤ g) (x : LowerRoot d → ℂ) :
    tensorMatrix (columnHeight mu) (lowerRootMatrix x)
      (shallowMonomialBasis mu a hmu g hgap hdepth) (highestBasisIndex mu) =
      ∏ r : LowerRoot d, x r ^ a r := by
  rw [shallowMonomialBasis, monomialBasis_coefficient mu a _ _
    (lowerRootMatrix_upper x) (lowerRootMatrix_diagonal x)]
  simp only [lowerRootMatrix_root]

end FreeEntropy.ExteriorRepresentation
