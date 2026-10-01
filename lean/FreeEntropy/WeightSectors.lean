/-
Copyright (c) 2026 Free Entropy formalization contributors.
See LICENSE and NOTICE in the repository root for license and attribution.
-/

import FreeEntropy.CartanChannel
import FreeEntropy.CasimirTrace

/-!
# Weight-sector projectors constructed from joint diagonal weights

The projectors are literal diagonal coordinate projections. Intertwining
the diagonal Cartan generators forces an intertwiner to preserve these
joint eigenspaces; the sector identities used by the cloning branches
then follow from matrix algebra.
-/

noncomputable section
open scoped BigOperators Matrix Kronecker ComplexOrder MatrixOrder
open Matrix

namespace FreeEntropy.WeightSectors
open CartanChannel

set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false

variable {I H K A B C : Type*} [Fintype H] [Fintype K] [Fintype A] [Fintype B] [Fintype C]
  [DecidableEq H] [DecidableEq K] [DecidableEq A] [DecidableEq B] [DecidableEq C]

local instance : DecidableEq (I → ℝ) := Classical.decEq _

def weightDiagonal (w : H → I → ℝ) (i : I) : Matrix H H ℂ :=
  diagonal (fun h => (w h i : ℂ))

def weightProjector (w : H → I → ℝ) (lam : I → ℝ) : Matrix H H ℂ := by
  classical
  exact diagonal (fun h => if w h = lam then 1 else 0)

theorem weightProjector_isStarProjection (w : H → I → ℝ) (lam : I → ℝ) :
    IsStarProjection (weightProjector w lam) := by
  classical
  simpa [weightProjector, CasimirTrace.coordinateSector] using CasimirTrace.coordinateSector_isStarProjection (Finset.univ.filter (fun h => w h = lam))

theorem weightProjector_trace (w : H → I → ℝ) (lam : I → ℝ) :
    (weightProjector w lam).trace = ((Finset.univ.filter (fun h => w h = lam)).card : ℂ) := by
  classical
  simp [weightProjector, Matrix.trace_diagonal]

theorem weightProjector_ne_zero_iff (w : H → I → ℝ) (lam : I → ℝ) :
    weightProjector w lam ≠ 0 ↔ ∃ h, w h = lam := by
  classical
  constructor
  · intro hp
    by_contra hn
    push_neg at hn
    apply hp
    simp [weightProjector, hn]
  · rintro ⟨h, hh⟩ hz
    have he := congrArg (fun M : Matrix H H ℂ => M h h) hz
    simp [weightProjector, hh] at he

/-- A nonzero matrix entry of a Cartan intertwiner joins equal joint weights. -/
theorem intertwiner_weight_eq (wH : H → I → ℝ) (wK : K → I → ℝ)
    (V : Matrix H K ℂ)
    (hV : ∀ i, weightDiagonal wH i * V = V * weightDiagonal wK i)
    (h : H) (k : K) (hnz : V h k ≠ 0) : wH h = wK k := by
  funext i
  have he := congrArg (fun M : Matrix H K ℂ => M h k) (hV i)
  simp only [weightDiagonal, Matrix.diagonal_mul, Matrix.mul_diagonal] at he
  apply Complex.ofReal_injective
  exact mul_right_cancel₀ hnz (he.trans (mul_comm _ _))

/-- Joint eigenspace projectors are preserved by a genuine Cartan intertwiner. -/
theorem weightProjector_intertwines (wH : H → I → ℝ) (wK : K → I → ℝ)
    (V : Matrix H K ℂ)
    (hV : ∀ i, weightDiagonal wH i * V = V * weightDiagonal wK i) (lam : I → ℝ) :
    weightProjector wH lam * V = V * weightProjector wK lam := by
  classical
  ext h k
  simp only [weightProjector, Matrix.diagonal_mul, Matrix.mul_diagonal]
  by_cases hnz : V h k = 0
  · simp [hnz]
  · rw [intertwiner_weight_eq wH wK V hV h k hnz]
    split_ifs <;> simp

def totalWeight (wA : A → I → ℝ) (wB : B → I → ℝ) (ab : A × B) : I → ℝ :=
  wA ab.1 + wB ab.2

theorem totalWeight_diagonal (wA : A → I → ℝ) (wB : B → I → ℝ) (i : I) :
    weightDiagonal (totalWeight wA wB) i =
      weightDiagonal wA i ⊗ₖ (1 : Matrix B B ℂ) +
        (1 : Matrix A A ℂ) ⊗ₖ weightDiagonal wB i := by
  ext ⟨a,b⟩ ⟨a',b'⟩
  by_cases ha : a = a' <;> by_cases hb : b = b' <;>
    simp [weightDiagonal, totalWeight, ha, hb, Complex.ofReal_add]

/-- Fixing the auxiliary basis vector shifts every source weight by its
actual auxiliary weight. No sector-preservation equation is assumed. -/
theorem basisEmbedding_weightProjector (wA : A → I → ℝ) (wB : B → I → ℝ)
    (k : B) (lam : I → ℝ) :
    weightProjector (totalWeight wA wB) (lam + wB k) * basisEmbedding (A := A) k =
      basisEmbedding (A := A) k * weightProjector wA lam := by
  classical
  ext ⟨a,b⟩ a'
  simp only [weightProjector, Matrix.diagonal_mul, Matrix.mul_diagonal]
  by_cases hb : b = k
  · subst b
    by_cases ha : a = a'
    · subst a'
      simp [basisEmbedding, totalWeight]
    · simp [basisEmbedding, ha]
  · simp [basisEmbedding, hb]

/-- The retained forward and reverse branch identities follow from two
ordinary sector-intertwining equations. -/
theorem branch_identities_of_sector_intertwining
    (S : Matrix H H ℂ) (Pm : Matrix A A ℂ) (Pn : Matrix C C ℂ)
    (V : Matrix H C ℂ) (J : Matrix H A ℂ)
    (hS : IsStarProjection S) (hPm : IsStarProjection Pm) (hPn : IsStarProjection Pn)
    (hJ : Jᴴ * J = 1) (hSV : S * V = V * Pn) (hSJ : S * J = J * Pm) :
    (V * Vᴴ) * (J * Pm * Jᴴ) * (V * Vᴴ) =
      (V * Pn * Vᴴ) * (J * Pm * Jᴴ) * (V * Pn * Vᴴ) ∧
    Jᴴ * (V * Pn * Vᴴ) * J =
      Jᴴ * ((J * Pm * Jᴴ) * (V * Pn * Vᴴ) * (J * Pm * Jᴴ)) * J ∧
    (J * Pm * Jᴴ) * S * (J * Pm * Jᴴ) = J * Pm * Jᴴ := by
  have hSH : Sᴴ = S := hS.isSelfAdjoint.star_eq
  have hmH : Pmᴴ = Pm := hPm.isSelfAdjoint.star_eq
  have hnH : Pnᴴ = Pn := hPn.isSelfAdjoint.star_eq
  have hVS : Vᴴ * S = Pn * Vᴴ := by
    simpa only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hSH, hnH]
      using congrArg Matrix.conjTranspose hSV
  have hJS : Jᴴ * S = Pm * Jᴴ := by
    simpa only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hSH, hmH]
      using congrArg Matrix.conjTranspose hSJ
  let P := V * Pn * Vᴴ
  let Q := J * Pm * Jᴴ
  have hSP : S * P = P := by
    change S * (V * Pn * Vᴴ) = V * Pn * Vᴴ
    calc
      _ = (S * V) * Pn * Vᴴ := by simp only [Matrix.mul_assoc]
      _ = V * Pn * Pn * Vᴴ := by rw [hSV]
      _ = _ := by rw [Matrix.mul_assoc V Pn Pn, hPn.isIdempotentElem.eq]
  have hSQ : S * Q = Q := by
    change S * (J * Pm * Jᴴ) = J * Pm * Jᴴ
    calc
      _ = (S * J) * Pm * Jᴴ := by simp only [Matrix.mul_assoc]
      _ = J * Pm * Pm * Jᴴ := by rw [hSJ]
      _ = _ := by rw [Matrix.mul_assoc J Pm Pm, hPm.isIdempotentElem.eq]
  have hPH : Pᴴ = P := by simp only [P, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_conjTranspose, hnH, Matrix.mul_assoc]
  have hQH : Qᴴ = Q := by simp only [Q, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_conjTranspose, hmH, Matrix.mul_assoc]
  have hPS : P * S = P := by
    simpa only [Matrix.conjTranspose_mul, hPH, hSH] using congrArg Matrix.conjTranspose hSP
  have hQS : Q * S = Q := by
    simpa only [Matrix.conjTranspose_mul, hQH, hSH] using congrArg Matrix.conjTranspose hSQ
  have hRleft : (V * Vᴴ) * S = P := by
    rw [Matrix.mul_assoc, hVS]
    exact (Matrix.mul_assoc V Pn Vᴴ).symm
  have hRright : S * (V * Vᴴ) = P := by
    rw [← Matrix.mul_assoc, hSV]
  have hJQ : Jᴴ * Q = Pm * Jᴴ := by
    change Jᴴ * (J * Pm * Jᴴ) = Pm * Jᴴ
    calc
      _ = (Jᴴ * J) * Pm * Jᴴ := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [hJ, Matrix.one_mul]
  have hQJ : Q * J = J * Pm := by
    change (J * Pm * Jᴴ) * J = J * Pm
    rw [Matrix.mul_assoc (J * Pm), hJ, Matrix.mul_one]
  have hQQ : Q * Q = Q := by
    change Q * (J * Pm * Jᴴ) = Q
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hQJ,
      Matrix.mul_assoc J Pm Pm, hPm.isIdempotentElem.eq]
  change (V * Vᴴ) * Q * (V * Vᴴ) = P * Q * P ∧
    Jᴴ * P * J = Jᴴ * (Q * P * Q) * J ∧ Q * S * Q = Q
  constructor
  · calc
      _ = (V * Vᴴ) * (S * Q * S) * (V * Vᴴ) := by rw [hSQ, hQS]
      _ = ((V * Vᴴ) * S) * Q * (S * (V * Vᴴ)) := by simp only [Matrix.mul_assoc]
      _ = P * Q * P := by rw [hRleft, hRright]
  constructor
  · calc
      _ = Jᴴ * (S * P * S) * J := by rw [hSP, hPS]
      _ = (Jᴴ * S) * P * (S * J) := by simp only [Matrix.mul_assoc]
      _ = (Pm * Jᴴ) * P * (J * Pm) := by rw [hJS, hSJ]
      _ = (Jᴴ * Q) * P * (Q * J) := by rw [hJQ, hQJ]
      _ = _ := by simp only [Matrix.mul_assoc]
  · rw [hQS, hQQ]

/-- Concrete diagonal weight data and Cartan intertwining discharge all
three weight-sector identities required by the Casimir cloning adapter. -/
theorem cloning_weight_sector_identities
    (wA : A → I → ℝ) (wB : B → I → ℝ) (wC : C → I → ℝ)
    (V : Matrix (A × B) C ℂ)
    (hintertwine : ∀ i,
      (weightDiagonal wA i ⊗ₖ (1 : Matrix B B ℂ) +
        (1 : Matrix A A ℂ) ⊗ₖ weightDiagonal wB i) * V = V * weightDiagonal wC i)
    (k : B) (lam : I → ℝ) :
    let Pm := weightProjector wA lam
    let Pn := weightProjector wC (lam + wB k)
    let S := weightProjector (totalWeight wA wB) (lam + wB k)
    let J := basisEmbedding (A := A) k
    (V * Vᴴ) * (J * Pm * Jᴴ) * (V * Vᴴ) =
      (V * Pn * Vᴴ) * (J * Pm * Jᴴ) * (V * Pn * Vᴴ) ∧
    Jᴴ * (V * Pn * Vᴴ) * J = Jᴴ * ((J * Pm * Jᴴ) * (V * Pn * Vᴴ) * (J * Pm * Jᴴ)) * J ∧
    (J * Pm * Jᴴ) * S * (J * Pm * Jᴴ) = J * Pm * Jᴴ := by
  apply branch_identities_of_sector_intertwining
    _ _ _ V (basisEmbedding (A := A) k)
    (weightProjector_isStarProjection _ _) (weightProjector_isStarProjection _ _)
    (weightProjector_isStarProjection _ _) (basisEmbedding_isometry k)
  · apply weightProjector_intertwines
    intro i
    rw [totalWeight_diagonal]
    exact hintertwine i
  · exact basisEmbedding_weightProjector wA wB k lam

end FreeEntropy.WeightSectors
