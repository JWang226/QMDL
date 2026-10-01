/-
Copyright (c) 2026 Free Entropy formalization contributors.
See LICENSE and NOTICE in the repository root for license and attribution.
-/

import FreeEntropy.ExteriorWeights
import Mathlib.LinearAlgebra.Matrix.Block

/-! Exact coordinate minors on the lower unitriangular orbit. Replacing the
last row of a highest exterior basis vector reads off one free matrix entry. -/
noncomputable section
open Matrix
open scoped BigOperators
namespace FreeEntropy.ExteriorRepresentation
set_option backward.isDefEq.respectTransparency false
variable {d : ℕ}

def replacementEmbedding (i j : Fin d) (hji : j ≤ i) : Fin (j.val + 1) ↪o Fin d :=
  OrderEmbedding.ofStrictMono
    (fun t => if ht : t.val < j.val then ⟨t.val, by omega⟩ else i) (by
      intro s t hst
      have hs : s.val < t.val := hst
      have ht := t.isLt
      have hji' : j.val ≤ i.val := hji
      dsimp
      split_ifs with hs' ht'
      · exact hs
      · change s.val < i.val; omega
      · omega
      · omega)

def replacementSubset (i j : Fin d) (hji : j ≤ i) : Index d (j.val + 1) :=
  Set.powersetCard.ofFinEmbEquiv (replacementEmbedding i j hji)

@[simp] theorem enumerate_replacement (i j : Fin d) (hji : j ≤ i) (t : Fin (j.val + 1)) :
    enumerate (replacementSubset i j hji) t = replacementEmbedding i j hji t := by
  simp [replacementSubset, enumerate]

@[simp] theorem replacementEmbedding_last (i j : Fin d) (hji : j ≤ i) :
    replacementEmbedding i j hji (Fin.last j.val) = i := by
  simp [replacementEmbedding]

theorem replacementEmbedding_castSucc (i j : Fin d) (hji : j ≤ i) (t : Fin j.val) :
    replacementEmbedding i j hji t.castSucc = ⟨t.val, by omega⟩ := by
  simp [replacementEmbedding, t.isLt]

/-- A literal lower unitriangular matrix has this exact exterior matrix
coefficient; no asymptotic estimate or representation identity is assumed. -/
theorem lowerUnitriangular_replacement_minor
    (L : Matrix (Fin d) (Fin d) ℂ)
    (hupper : ∀ a b, a < b → L a b = 0) (hdiag : ∀ a, L a a = 1)
    (i j : Fin d) (hji : j ≤ i) :
    exteriorMatrix (j.val + 1) L (replacementSubset i j hji)
      (first (Nat.succ_le_of_lt j.isLt)) = L i j := by
  rw [exteriorMatrix_apply]
  let M := L.submatrix (enumerate (replacementSubset i j hji))
    (enumerate (first (Nat.succ_le_of_lt j.isLt)))
  have htri : M.BlockTriangular OrderDual.toDual := by
    intro a b hab
    have hab' : a.val < b.val := hab
    have ha : a.val < j.val := by have := b.isLt; omega
    change L (enumerate (replacementSubset i j hji) a)
      (enumerate (first (Nat.succ_le_of_lt j.isLt)) b) = 0
    rw [enumerate_replacement, enumerate_first]
    have hrow : replacementEmbedding i j hji a = ⟨a.val, by omega⟩ := by
      simp [replacementEmbedding, ha]
    rw [hrow]
    exact hupper _ _ hab'
  change M.det = _
  rw [Matrix.det_of_lowerTriangular M htri, Fin.prod_univ_castSucc]
  have hfirst (t : Fin j.val) : M t.castSucc t.castSucc = 1 := by
    dsimp [M]
    rw [enumerate_replacement, replacementEmbedding_castSucc, enumerate_first]
    exact hdiag _
  have hlast : M (Fin.last j.val) (Fin.last j.val) = L i j := by
    dsimp [M]
    rw [enumerate_replacement, replacementEmbedding_last, enumerate_first]
    rfl
  simp only [hfirst, Finset.prod_const_one, hlast, one_mul]

end FreeEntropy.ExteriorRepresentation
