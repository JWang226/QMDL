/-
Copyright (c) 2026 Free Entropy formalization contributors.
See LICENSE and NOTICE in the repository root for license and attribution.
-/

import FreeEntropy.CartanChoi

/-! The reverse Cartan map has the conjugate-flipped forward Choi support.
All Choi matrices, projections, and embeddings are literal finite matrices. -/
noncomputable section
open Matrix
open scoped BigOperators ComplexOrder MatrixOrder
namespace FreeEntropy.CartanChoi
open CartanChannel CartanLieCloning LieMatrixCasimir
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
variable {d : ℕ} {A B C : Type*} [Fintype A] [DecidableEq A]
  [Fintype B] [DecidableEq B] [Fintype C] [DecidableEq C]

/-- Swap the input/output legs and conjugate every entry. -/
def flipConjugate (J : Matrix (A × C) (A × C) ℂ) : Matrix (C × A) (C × A) ℂ :=
  fun ca db => star (J ca.swap db.swap)

/-- The explicit isometric dual copy in target-dual × source. -/
def reverseEmbedding (V : Matrix (A × B) C ℂ) : Matrix (C × A) B ℂ :=
  fun ca b => star (embedding V ca.swap b)

/-- The reverse Choi support is the conjugate-flipped forward support. -/
def reverseProjector (V : Matrix (A × B) C ℂ) : Matrix (C × A) (C × A) ℂ :=
  flipConjugate (projector V)

theorem reverseEmbedding_projector (V : Matrix (A × B) C ℂ) :
    reverseEmbedding V * (reverseEmbedding V)ᴴ = reverseProjector V := by
  rw [reverseProjector, ← embedding_projector]
  ext ⟨c,a⟩ ⟨c',a'⟩
  simp [flipConjugate, reverseEmbedding, Matrix.mul_apply, Matrix.conjTranspose_apply]

theorem reverseEmbedding_isometry [Nonempty B] [Nonempty C]
    (M : CyclicWeightModel d A) (N : CyclicWeightModel d B) (S : CyclicWeightModel d C)
    (V : Matrix (A × B) C ℂ) (hV : Vᴴ * V = 1)
    (hE : ∀ i j, (M.generators.tensor N.generators).E i j * V = V * S.generators.E i j) :
    (reverseEmbedding V)ᴴ * reverseEmbedding V = 1 := by
  have hW := embedding_isometry M N S V hV hE
  ext b b'
  change (∑ ca : C × A, star (star (embedding V ca.swap b)) * star (embedding V ca.swap b')) = _
  simp only [star_star, Fintype.sum_prod_type, Prod.swap_prod_mk]
  rw [Finset.sum_comm]
  have he := congrArg star (congrArg (fun X : Matrix B B ℂ => X b b') hW)
  simpa only [Matrix.mul_apply, Matrix.conjTranspose_apply, Fintype.sum_prod_type,
    map_sum, star_sum, StarMul.star_mul, star_star, apply_ite, star_one, star_zero, Matrix.one_apply, mul_comm] using he

theorem reverseProjector_hermitian (V : Matrix (A × B) C ℂ) :
    (reverseProjector V).IsHermitian := by
  rw [← reverseEmbedding_projector]
  exact Matrix.isHermitian_mul_conjTranspose_self _

theorem reverseProjector_positive (V : Matrix (A × B) C ℂ) :
    (reverseProjector V).PosSemidef := by
  rw [← reverseEmbedding_projector]
  exact Matrix.posSemidef_self_mul_conjTranspose _

theorem reverseProjector_idempotent [Nonempty B] [Nonempty C]
    (M : CyclicWeightModel d A) (N : CyclicWeightModel d B) (S : CyclicWeightModel d C)
    (V : Matrix (A × B) C ℂ) (hV : Vᴴ * V = 1)
    (hE : ∀ i j, (M.generators.tensor N.generators).E i j * V = V * S.generators.E i j) :
    reverseProjector V * reverseProjector V = reverseProjector V := by
  rw [← reverseEmbedding_projector]
  simp only [Matrix.mul_assoc, ← Matrix.mul_assoc (reverseEmbedding V)ᴴ (reverseEmbedding V),
    reverseEmbedding_isometry M N S V hV hE, Matrix.one_mul]

theorem reverseProjector_rank [Nonempty B] [Nonempty C]
    (M : CyclicWeightModel d A) (N : CyclicWeightModel d B) (S : CyclicWeightModel d C)
    (V : Matrix (A × B) C ℂ) (hV : Vᴴ * V = 1)
    (hE : ∀ i j, (M.generators.tensor N.generators).E i j * V = V * S.generators.E i j) :
    (reverseProjector V).rank = Fintype.card B := by
  rw [← reverseEmbedding_projector, Matrix.rank_self_mul_conjTranspose,
    ← Matrix.rank_conjTranspose_mul_self, reverseEmbedding_isometry M N S V hV hE, Matrix.rank_one]

theorem choi_reverseMap (V : Matrix (A × B) C ℂ) :
    choi (reverseMap V) = flipConjugate ((reshuffle V)ᴴ * reshuffle V) := by
  ext ⟨c,a⟩ ⟨c',a'⟩
  simp [choi, reverseMap_eq_kraus, Channels.krausMap, reverseKraus,
    Matrix.mul_apply, Matrix.sum_apply, Matrix.single_apply, flipConjugate,
    reshuffle, Matrix.conjTranspose_apply, ite_and]

theorem choi_reverse_eq_scaled_projector [Nonempty B] [Nonempty C]
    (V : Matrix (A × B) C ℂ) :
    choi (reverseMap V) = ((Fintype.card C : ℝ) / (Fintype.card B : ℝ)) • reverseProjector V := by
  rw [choi_reverseMap]
  have hb : (Fintype.card B : ℝ) ≠ 0 := by exact_mod_cast (Fintype.card_ne_zero : Fintype.card B ≠ 0)
  have hc : (Fintype.card C : ℝ) ≠ 0 := by exact_mod_cast (Fintype.card_ne_zero : Fintype.card C ≠ 0)
  have he : (Fintype.card C : ℝ) / (Fintype.card B : ℝ) *
      ((Fintype.card B : ℝ) / (Fintype.card C : ℝ)) = 1 := by field_simp
  ext x y
  simp only [reverseProjector, projector, flipConjugate, Matrix.smul_apply, star_smul,
    star_trivial, smul_smul, he, one_smul]

omit [Fintype C] [DecidableEq C] in
/-- Reconstruction holds for every complex-linear map, with no positivity
or invertibility restrictions on its input matrix. -/
theorem choiMap_choi_linear (f : Matrix A A ℂ →ₗ[ℂ] Matrix C C ℂ) (X : Matrix A A ℂ) :
    choiMap (choi f) X = f X := by
  have hX : (∑ a, ∑ a', X a a' • Matrix.single a a' (1 : ℂ)) = X := by
    simpa only [Matrix.smul_single, smul_eq_mul, mul_one] using Matrix.sum_sum_single X
  rw [← hX]
  simp only [map_sum, map_smul]
  ext c c'
  simp [choiMap, choi, Matrix.sum_apply, Matrix.smul_apply, Matrix.single_apply, ite_and]

theorem choiMap_reverseMap (V : Matrix (A × B) C ℂ) (Y : Matrix C C ℂ) :
    choiMap (choi (reverseMap V)) Y = reverseMap V Y := by
  let f : Matrix C C ℂ →ₗ[ℂ] Matrix A A ℂ :=
    { toFun := Channels.krausMap (reverseKraus V)
      map_add' := Channels.krausMap_add (reverseKraus V)
      map_smul' := Channels.krausMap_smul (reverseKraus V) }
  have he : reverseMap V = f := funext (reverseMap_eq_kraus V)
  rw [he]
  exact choiMap_choi_linear f Y

end FreeEntropy.CartanChoi
