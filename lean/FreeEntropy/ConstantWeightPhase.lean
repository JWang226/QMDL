/-
Copyright (c) 2026 Free Entropy formalization contributors.
See LICENSE and NOTICE in the repository root for license and attribution.
-/

import FreeEntropy.CartanGroupCovariance
import FreeEntropy.CanonicalDimension

/-! Constant highest rows give genuine one-dimensional representations.
Their scalar unitary action realizes the phase needed for signed twists. -/
noncomputable section
open Matrix
open scoped BigOperators Kronecker
namespace FreeEntropy.CartanLieCloning
open LieMatrixCasimir
set_option backward.isDefEq.respectTransparency false
variable {d : ℕ} {A : Type*} [Fintype A] [DecidableEq A] [Nonempty A] [Subsingleton A]

theorem CyclicWeightModel.subsingleton_generators (M : CyclicWeightModel d A)
    (c : ℝ) (hrow : ∀ i, M.row i = c) (i j : Fin d) :
    M.generators.E i j = if i = j then c • 1 else 0 := by
  have hr (i j : Fin d) (hij : i < j) : M.generators.E i j = 0 := by
    apply Matrix.ext
    intro a b
    have h := M.highest_basis_raise M.highestBasis M.highestBasis_weight i j hij a
    simpa only [Subsingleton.elim b M.highestBasis] using h
  by_cases hij : i = j
  · subst j
    rw [if_pos rfl, M.diagonal]
    apply Matrix.ext
    intro a b
    have hw : M.weight a i = c := by
      rw [Subsingleton.elim a M.highestBasis, M.highestBasis_weight, hrow]
    rw [Subsingleton.elim b a]
    simp [WeightSectors.weightDiagonal, hw]
  · rw [if_neg hij]
    rcases lt_or_gt_of_ne hij with h | h
    · exact hr i j h
    · have he := congrArg Matrix.conjTranspose (hr j i h)
      simpa only [M.generators.adjoint, Matrix.conjTranspose_zero] using he

end FreeEntropy.CartanLieCloning

namespace FreeEntropy.ExteriorRepresentation
set_option backward.isDefEq.respectTransparency false
variable {d : ℕ}

theorem constantWeight_dimension (c : ℕ) (hd : 0 < d) :
    Module.finrank ℂ (highestSubspace (fun _ : Fin d => c)) = 1 := by
  have h := canonical_dimension_fullWeyl (d := d) (fun _ => c) (fun _ _ _ => le_rfl) hd
  have hp : Weyl.activeProduct d d (fun _ => (c : ℝ)) = 1 := by
    apply Finset.prod_eq_one
    intro p hp
    have hlt := (Weyl.mem_activeRoots.mp hp).2.1
    have hn : ((p.2 - p.1 : ℕ) : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt (Nat.sub_pos_of_lt hlt)
    simp only [sub_self, zero_add, div_self hn]
  exact_mod_cast h.trans hp

theorem constantWeightIndex_subsingleton (c : ℕ) (hd : 0 < d) :
    Subsingleton (IrrepIndex (fun _ : Fin d => c)) := by
  apply Fintype.card_le_one_iff_subsingleton.mp
  simpa only [IrrepIndex, Fintype.card_fin] using (constantWeight_dimension c hd).le

end FreeEntropy.ExteriorRepresentation

namespace FreeEntropy.CartanChannel
set_option backward.isDefEq.respectTransparency false
variable {A B : Type*} [Fintype A] [DecidableEq A]
  [Fintype B] [DecidableEq B] [Subsingleton B]

theorem subsingleton_matrix_scalar (W : Matrix B B ℂ) (k : B) : W = W k k • 1 := by
  apply Matrix.ext
  intro i j
  rw [Subsingleton.elim i k, Subsingleton.elim j k]
  simp

theorem subsingleton_unitary_phase (W : Matrix B B ℂ) (k : B) (hW : Wᴴ * W = 1) :
    W k k * star (W k k) = 1 := by
  have he := hW
  rw [subsingleton_matrix_scalar W k] at he
  have h := congrArg (fun X : Matrix B B ℂ => X k k) he
  simp only [Matrix.conjTranspose_smul, Matrix.conjTranspose_one, Matrix.smul_mul,
    Matrix.mul_smul, Matrix.one_mul, smul_smul, Matrix.smul_apply, Matrix.one_apply_eq,
    smul_eq_mul, mul_one] at h
  simpa only [mul_comm] using h

/-- With a one-dimensional spectator the canonical basis embedding is onto. -/
theorem basisEmbedding_coisometry (k : B) :
    basisEmbedding (A := A) k * (basisEmbedding (A := A) k)ᴴ = 1 := by
  apply Matrix.ext
  intro a b
  have ha : a.2 = k := Subsingleton.elim _ _
  have hb : b.2 = k := Subsingleton.elim _ _
  simp [basisEmbedding, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply,
    ha, hb, Prod.ext_iff]

/-- The spectator action is exactly a scalar phase on the original carrier. -/
theorem basisEmbedding_phase (U : Matrix A A ℂ) (W : Matrix B B ℂ) (k : B) :
    (U ⊗ₖ W) * basisEmbedding k = basisEmbedding k * (W k k • U) := by
  apply Matrix.ext
  intro a b
  have ha : a.2 = k := Subsingleton.elim _ _
  simp [basisEmbedding, Matrix.mul_apply, Matrix.kronecker_apply, Fintype.sum_prod_type,
    Matrix.smul_apply, Matrix.one_apply, ha, mul_comm]

end FreeEntropy.CartanChannel
