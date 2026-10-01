/-
Copyright (c) 2026 Free Entropy formalization contributors.
See LICENSE and NOTICE in the repository root for license and attribution.
-/

import FreeEntropy.CartanReshuffle
import FreeEntropy.SpecifiedCloningChannels
import Mathlib.LinearAlgebra.Matrix.Rank

/-! The Cartan formula has a normalized irreducible-range Choi projector. -/
noncomputable section
open Matrix
open scoped BigOperators Kronecker ComplexOrder MatrixOrder
namespace FreeEntropy.CartanChoi
open LieMatrixCasimir CartanLieCloning CartanChannel
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
variable {d : ℕ} {A B C : Type*} [Fintype A] [DecidableEq A]
  [Fintype B] [DecidableEq B] [Fintype C] [DecidableEq C]

/-- Unnormalized Choi matrix, in input-dual × output coordinates. -/
def choi (f : Matrix A A ℂ → Matrix C C ℂ) : Matrix (A × C) (A × C) ℂ :=
  fun ac bd => f (Matrix.single ac.1 bd.1 1) ac.2 bd.2

/-- Contraction formula recovering a map from its Choi matrix. -/
def choiMap (J : Matrix (A × C) (A × C) ℂ) (X : Matrix A A ℂ) : Matrix C C ℂ :=
  fun c c' => ∑ a, ∑ a', X a a' * J (a,c) (a',c')

theorem choi_sectorMap (V : Matrix (A × B) C ℂ) (din dout : ℝ) :
    choi (sectorMap din dout V) = (din / dout) • (reshuffle V)ᴴ * reshuffle V := by
  ext ⟨a,c⟩ ⟨a',c'⟩
  simp [choi, sectorMap, core_eq_kraus, Channels.krausMap, sliceKraus,
    Matrix.mul_apply, Matrix.sum_apply, Matrix.single_apply, reshuffle, Matrix.conjTranspose_apply,
    Finset.sum_mul, Finset.mul_sum, mul_assoc, ite_and]

theorem choiMap_sectorMap (V : Matrix (A × B) C ℂ) (din dout : ℝ) (X : Matrix A A ℂ) :
    choiMap (choi (sectorMap din dout V)) X = sectorMap din dout V X := by
  rw [choi_sectorMap]
  ext c c'
  simp only [choiMap, sectorMap, core_eq_kraus, Channels.krausMap, sliceKraus,
    Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.sum_apply,
    Matrix.smul_apply, reshuffle, Finset.mul_sum, Finset.sum_mul, Complex.real_smul,
    smul_eq_mul, star_star]
  calc
    _ = ∑ a, ∑ b, ∑ a', X a a' * ((din / dout : ℝ) * star (V (a,b) c) * V (a',b) c') := by
      apply Finset.sum_congr rfl
      intro a _
      exact Finset.sum_comm
    _ = ∑ b, ∑ a, ∑ a', X a a' * ((din / dout : ℝ) * star (V (a,b) c) * V (a',b) c') := Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro b _
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro a' _
      apply Finset.sum_congr rfl
      intro a _
      ring

theorem reshuffle_trace (V : Matrix (A × B) C ℂ) :
    ((reshuffle V) * (reshuffle V)ᴴ).trace = (Vᴴ * V).trace := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply,
    reshuffle, Fintype.sum_prod_type]
  calc
    _ = ∑ b, ∑ c, ∑ a, V (a,b) c * star (V (a,b) c) := by
      apply Finset.sum_congr rfl
      intro b _
      exact Finset.sum_comm
    _ = ∑ c, ∑ b, ∑ a, V (a,b) c * star (V (a,b) c) := Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro c _
      rw [Finset.sum_comm]
      simp only [mul_comm]

/-- Irreducibility of the actual auxiliary module fixes the Gram constant. -/
theorem reshuffle_gram [Nonempty B]
    (M : CyclicWeightModel d A) (N : CyclicWeightModel d B) (S : CyclicWeightModel d C)
    (V : Matrix (A × B) C ℂ) (hV : Vᴴ * V = 1)
    (hE : ∀ i j, (M.generators.tensor N.generators).E i j * V = V * S.generators.E i j) :
    reshuffle V * (reshuffle V)ᴴ =
      ((Fintype.card C : ℝ) / (Fintype.card B : ℝ)) • (1 : Matrix B B ℂ) := by
  have hF := (reshuffle_intertwines_iff M.generators N.generators S.generators V).mp hE
  have hc (i j : Fin d) :
      (reshuffle V * (reshuffle V)ᴴ) * N.generators.E i j =
      N.generators.E i j * (reshuffle V * (reshuffle V)ᴴ) := by
    have ha := congrArg Matrix.conjTranspose (hF j i)
    simp only [Matrix.conjTranspose_mul, Generators.adjoint] at ha
    rw [Matrix.mul_assoc, ha, ← Matrix.mul_assoc, ← hF, Matrix.mul_assoc]
  obtain ⟨c, he⟩ := LiePBW.commutant_scalar_of_highest N.generators (fun i => (N.row i : ℂ))
    N.highestVector N.highestVector_ne_zero N.vector_weight N.vector_raise N.vector_cyclic
    (reshuffle V * (reshuffle V)ᴴ) hc
  have ht := congrArg Matrix.trace he
  rw [reshuffle_trace, hV] at ht
  simp only [Matrix.trace_one, Matrix.trace_smul, smul_eq_mul] at ht
  have hB : (Fintype.card B : ℂ) ≠ 0 := by exact_mod_cast (Fintype.card_ne_zero : Fintype.card B ≠ 0)
  have hec : c = (Fintype.card C : ℂ) / (Fintype.card B : ℂ) :=
    (eq_div_iff hB).mpr ht.symm
  rw [he, hec]
  ext i j
  simp [Matrix.smul_apply, Complex.real_smul]

/-- The explicit support projection of the Choi matrix. -/
def projector (V : Matrix (A × B) C ℂ) : Matrix (A × C) (A × C) ℂ :=
  ((Fintype.card B : ℝ) / (Fintype.card C : ℝ)) • ((reshuffle V)ᴴ * reshuffle V)

theorem projector_hermitian (V : Matrix (A × B) C ℂ) : (projector V).IsHermitian := by
  change (projector V)ᴴ = projector V
  simp [projector, Matrix.conjTranspose_smul, Matrix.conjTranspose_mul]

theorem projector_positive (V : Matrix (A × B) C ℂ) : (projector V).PosSemidef := by
  exact (Matrix.posSemidef_conjTranspose_mul_self (reshuffle V)).smul (by positivity)

theorem projector_idempotent [Nonempty B] [Nonempty C]
    (M : CyclicWeightModel d A) (N : CyclicWeightModel d B) (S : CyclicWeightModel d C)
    (V : Matrix (A × B) C ℂ) (hV : Vᴴ * V = 1)
    (hE : ∀ i j, (M.generators.tensor N.generators).E i j * V = V * S.generators.E i j) :
    projector V * projector V = projector V := by
  have hb : (Fintype.card B : ℝ) ≠ 0 := by exact_mod_cast (Fintype.card_ne_zero : Fintype.card B ≠ 0)
  have hc : (Fintype.card C : ℝ) ≠ 0 := by exact_mod_cast (Fintype.card_ne_zero : Fintype.card C ≠ 0)
  have hq : ((Fintype.card B : ℝ) / Fintype.card C) *
      (((Fintype.card B : ℝ) / Fintype.card C) * ((Fintype.card C : ℝ) / Fintype.card B)) =
      (Fintype.card B : ℝ) / Fintype.card C := by field_simp
  simp only [projector, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  rw [Matrix.mul_assoc, ← Matrix.mul_assoc (reshuffle V), reshuffle_gram M N S V hV hE]
  simp only [Matrix.smul_mul, Matrix.one_mul, Matrix.mul_smul, smul_smul]
  congr 1
  nlinarith [hq]

theorem choi_eq_scaled_projector [Nonempty B] [Nonempty C]
    (V : Matrix (A × B) C ℂ) :
    choi (sectorMap (Fintype.card A) (Fintype.card C) V) =
      ((Fintype.card A : ℝ) / (Fintype.card B : ℝ)) • projector V := by
  have hb : (Fintype.card B : ℝ) ≠ 0 := by exact_mod_cast (Fintype.card_ne_zero : Fintype.card B ≠ 0)
  rw [choi_sectorMap]
  simp only [projector, Matrix.smul_mul, smul_smul]
  congr 1
  field_simp

/-- An actual isometric copy of the auxiliary module in input-dual × output. -/
def embedding (V : Matrix (A × B) C ℂ) : Matrix (A × C) B ℂ :=
  Real.sqrt ((Fintype.card B : ℝ) / (Fintype.card C : ℝ)) • (reshuffle V)ᴴ

theorem embedding_projector (V : Matrix (A × B) C ℂ) :
    embedding V * (embedding V)ᴴ = projector V := by
  simp only [embedding, Matrix.conjTranspose_smul, star_trivial,
    Matrix.conjTranspose_conjTranspose, Matrix.smul_mul, Matrix.mul_smul,
    smul_smul, Real.mul_self_sqrt (show 0 ≤ (Fintype.card B : ℝ) / Fintype.card C by positivity), projector]

theorem embedding_isometry [Nonempty B] [Nonempty C]
    (M : CyclicWeightModel d A) (N : CyclicWeightModel d B) (S : CyclicWeightModel d C)
    (V : Matrix (A × B) C ℂ) (hV : Vᴴ * V = 1)
    (hE : ∀ i j, (M.generators.tensor N.generators).E i j * V = V * S.generators.E i j) :
    (embedding V)ᴴ * embedding V = 1 := by
  have hb : (Fintype.card B : ℝ) ≠ 0 := by exact_mod_cast (Fintype.card_ne_zero : Fintype.card B ≠ 0)
  have hc : (Fintype.card C : ℝ) ≠ 0 := by exact_mod_cast (Fintype.card_ne_zero : Fintype.card C ≠ 0)
  have hq : ((Fintype.card B : ℝ) / Fintype.card C) *
      ((Fintype.card C : ℝ) / Fintype.card B) = 1 := by field_simp
  simp only [embedding, Matrix.conjTranspose_smul, star_trivial,
    Matrix.conjTranspose_conjTranspose, Matrix.smul_mul, Matrix.mul_smul,
    smul_smul, Real.mul_self_sqrt (show 0 ≤ (Fintype.card B : ℝ) / Fintype.card C by positivity),
    reshuffle_gram M N S V hV hE]
  rw [← mul_assoc, Real.mul_self_sqrt (show 0 ≤ (Fintype.card B : ℝ) / Fintype.card C by positivity), hq, one_smul]

theorem embedding_intertwines (M : Generators d A) (N : Generators d B) (S : Generators d C)
    (V : Matrix (A × B) C ℂ)
    (hE : ∀ i j, (M.tensor N).E i j * V = V * S.E i j) (i j : Fin d) :
    (M.dual.tensor S).E i j * embedding V = embedding V * N.E i j := by
  have ha := congrArg Matrix.conjTranspose ((reshuffle_intertwines_iff M N S V).mp hE j i)
  simp only [Matrix.conjTranspose_mul, Generators.adjoint] at ha
  simpa only [embedding, Matrix.mul_smul, Matrix.smul_mul] using congrArg
    (fun T => Real.sqrt ((Fintype.card B : ℝ) / (Fintype.card C : ℝ)) • T) ha.symm

theorem projector_rank [Nonempty B] [Nonempty C]
    (M : CyclicWeightModel d A) (N : CyclicWeightModel d B) (S : CyclicWeightModel d C)
    (V : Matrix (A × B) C ℂ) (hV : Vᴴ * V = 1)
    (hE : ∀ i j, (M.generators.tensor N.generators).E i j * V = V * S.generators.E i j) :
    (projector V).rank = Fintype.card B := by
  rw [← embedding_projector, Matrix.rank_self_mul_conjTranspose,
    ← Matrix.rank_conjTranspose_mul_self, embedding_isometry M N S V hV hE, Matrix.rank_one]

theorem projector_trace [Nonempty B] [Nonempty C]
    (M : CyclicWeightModel d A) (N : CyclicWeightModel d B) (S : CyclicWeightModel d C)
    (V : Matrix (A × B) C ℂ) (hV : Vᴴ * V = 1)
    (hE : ∀ i j, (M.generators.tensor N.generators).E i j * V = V * S.generators.E i j) :
    (projector V).trace = Fintype.card B := by
  rw [← embedding_projector, Matrix.trace_mul_comm,
    embedding_isometry M N S V hV hE, Matrix.trace_one]

end FreeEntropy.CartanChoi
