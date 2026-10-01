/-
Copyright (c) 2026 Free Entropy formalization contributors.
See LICENSE and NOTICE in the repository root for license and attribution.
-/

import FreeEntropy.CanonicalCartanCovariance
import FreeEntropy.CanonicalFullCloning

/-! At zero row difference the actual Cartan formula itself is the identity.
This identifies the convenience identity branch with the manuscript's
constructed generalized cloning channels. -/
noncomputable section
open Matrix
open scoped BigOperators Kronecker
namespace FreeEntropy.CartanLieCloning
open CartanChannel LieMatrixCasimir
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
variable {d : ℕ} {A B : Type*} [Fintype A] [DecidableEq A] [Nonempty A]
  [Fintype B] [DecidableEq B] [Nonempty B] [Subsingleton B]

/-- A Cartan inclusion with a trivial one-dimensional environment differs
from the identity inclusion by a unit scalar only. -/
theorem CyclicWeightModel.trivial_environment_phase (M : CyclicWeightModel d A)
    (N : CyclicWeightModel d B) (hrow : ∀ i, N.row i = 0)
    (V : Matrix (A × B) A ℂ) (hV : Vᴴ * V = 1)
    (hVE : ∀ i j, (M.generators.tensor N.generators).E i j * V = V * M.generators.E i j)
    (k : B) : ∃ a : ℂ, a * star a = 1 ∧ V = a • basisEmbedding k := by
  let Bm : Matrix (A × B) A ℂ := basisEmbedding k
  have hB : Bmᴴ * Bm = 1 := basisEmbedding_isometry k
  have hB' : Bm * Bmᴴ = 1 := basisEmbedding_coisometry k
  have hN (i j : Fin d) : N.generators.E i j = 0 := by
    rw [N.subsingleton_generators 0 hrow]
    split_ifs <;> simp
  have hBE (i j : Fin d) :
      (M.generators.E i j ⊗ₖ (1 : Matrix B B ℂ)) * Bm = Bm * M.generators.E i j := by
    simpa only [Matrix.one_apply_eq, one_smul] using basisEmbedding_phase (M.generators.E i j) (1 : Matrix B B ℂ) k
  have hBadj (i j : Fin d) :
      Bmᴴ * (M.generators.E i j ⊗ₖ (1 : Matrix B B ℂ)) = M.generators.E i j * Bmᴴ := by
    simpa only [Matrix.conjTranspose_mul, Matrix.conjTranspose_kronecker,
      Matrix.conjTranspose_one, M.generators.adjoint] using congrArg Matrix.conjTranspose (hBE j i)
  have hcomm (i j : Fin d) : (Bmᴴ * V) * M.generators.E i j = M.generators.E i j * (Bmᴴ * V) := by
    have he := hVE i j
    simp only [Generators.tensor, hN, Matrix.kronecker_zero, add_zero] at he
    rw [Matrix.mul_assoc, ← he, ← Matrix.mul_assoc, hBadj, Matrix.mul_assoc]
  obtain ⟨a, ha⟩ := LiePBW.commutant_scalar_of_highest M.generators
    (fun i => (M.row i : ℂ)) M.highestVector M.highestVector_ne_zero M.vector_weight
    M.vector_raise M.vector_cyclic (Bmᴴ * V) hcomm
  have heq : V = a • Bm := by
    have he := congrArg (fun X => Bm * X) ha
    simpa only [← Matrix.mul_assoc, hB', Matrix.one_mul, Matrix.mul_smul, Matrix.mul_one] using he
  refine ⟨a, ?_, heq⟩
  have hiso := hV
  rw [heq, Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, hB] at hiso
  have he := congrArg (fun X : Matrix A A ℂ => X M.highestBasis M.highestBasis) hiso
  simpa only [Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one, one_mul, mul_comm] using he

theorem trivial_environment_maps_identity (V : Matrix (A × B) A ℂ) (k : B)
    (a : ℂ) (ha : a * star a = 1) (hV : V = a • basisEmbedding k) (X : Matrix A A ℂ) :
    sectorMap (Fintype.card A) (Fintype.card A) V X = X ∧ reverseMap V X = X := by
  letI : Unique B := ⟨⟨k⟩, fun b => Subsingleton.elim b k⟩
  let Bm : Matrix (A × B) A ℂ := basisEmbedding k
  have hB : Bmᴴ * Bm = 1 := basisEmbedding_isometry k
  have hB' : Bm * Bmᴴ = 1 := basisEmbedding_coisometry k
  have hBX : (X ⊗ₖ (1 : Matrix B B ℂ)) * Bm = Bm * X := by
    simpa only [Matrix.one_apply_eq, one_smul] using basisEmbedding_phase X (1 : Matrix B B ℂ) k
  have hcore : Bmᴴ * (X ⊗ₖ (1 : Matrix B B ℂ)) * Bm = X := by
    rw [Matrix.mul_assoc, hBX, ← Matrix.mul_assoc, hB, Matrix.one_mul]
  have hemb : Bm * X * Bmᴴ = X ⊗ₖ (1 : Matrix B B ℂ) := by
    rw [← hBX, Matrix.mul_assoc, hB', Matrix.mul_one]
  have hpart : partialTrace (X ⊗ₖ (1 : Matrix B B ℂ)) = X := by
    apply Matrix.ext
    intro i j
    simp [partialTrace, Matrix.kronecker_apply]
  have hphase : star a * a = 1 := by simpa only [mul_comm] using ha
  have hc : (Fintype.card A : ℝ) ≠ 0 := by exact_mod_cast (Fintype.card_ne_zero : Fintype.card A ≠ 0)
  constructor
  · rw [sectorMap, div_self hc, one_smul, hV]
    change (a • Bm)ᴴ * (X ⊗ₖ (1 : Matrix B B ℂ)) * (a • Bm) = X
    simp only [Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
      ha, hphase, one_smul, hcore]
  · rw [reverseMap, hV]
    change partialTrace ((a • Bm) * X * (a • Bm)ᴴ) = X
    simp only [Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
      ha, hphase, one_smul, hemb, hpart]

end FreeEntropy.CartanLieCloning

namespace FreeEntropy.ExteriorRepresentation
open CartanLieCloning CartanChannel
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
variable {d : ℕ}
local instance self_ci_nonempty (mu : Fin d → ℕ) : Nonempty (IrrepIndex mu) :=
  Fin.pos_iff_nonempty.mp (irrep_dimension_pos mu)

/-- At zero row difference both actual Cartan formulas are the identity maps,
not merely maps that happen to fix the distinguished state. -/
theorem canonicalCartan_self_apply (mu : Fin d → ℕ) (hmu : Antitone mu)
    (hinc : Antitone (fun i => (mu i : ℝ) - (mu i : ℝ))) (hd : 0 < d)
    (X : Matrix (IrrepIndex mu) (IrrepIndex mu) ℂ) :
    (canonicalCartanForward mu mu hmu hmu hinc).toFun X = X ∧
      (canonicalCartanReverse mu mu hmu hmu hinc).toFun X = X := by
  have haux : auxiliaryRow mu mu = fun _ => auxiliaryShift mu := by
    funext i
    have hi := le_auxiliaryShift mu i
    change mu i + (auxiliaryShift mu - mu i) = auxiliaryShift mu
    omega
  letI : Subsingleton (IrrepIndex (auxiliaryRow mu mu)) := by
    rw [haux]
    exact constantWeightIndex_subsingleton (auxiliaryShift mu) hd
  let M := canonicalWeightModel mu
  let N := canonicalAuxiliaryModel mu mu
  let hrow := canonicalAuxiliaryModel_hrow mu mu hmu hmu hinc
  let V := specifiedCartanEmbedding M N M hrow
  have hN : ∀ i, N.row i = 0 := by
    intro i
    change (canonicalAuxiliaryModel mu mu).row i = 0
    rw [canonicalAuxiliaryModel_row mu mu hinc]
    exact sub_self _
  obtain ⟨a, ha, he⟩ := M.trivial_environment_phase N hN V
    (specifiedCartanEmbedding_isometry M N M hrow)
    (specifiedCartanEmbedding_intertwines M N M hrow) N.highestBasis
  have h := trivial_environment_maps_identity V N.highestBasis a ha he X
  simpa only [canonicalCartanForward, canonicalCartanReverse, specifiedForward, specifiedReverse,
    cartanChannel_apply, reverseChannel_apply, reverseMap, M, N, V, hrow] using h

/-- The total forward map uses exactly the Cartan formula also at zero difference. -/
theorem canonicalForward_eq_cartan_apply (mu nu : Fin d → ℕ) (hmu : Antitone mu)
    (hnu : Antitone nu) (hinc : Antitone (fun i => (nu i : ℝ) - (mu i : ℝ)))
    (hd : 0 < d) (X : Matrix (IrrepIndex mu) (IrrepIndex mu) ℂ) :
    (canonicalForward mu nu hmu hnu hinc).toFun X =
      (canonicalCartanForward mu nu hmu hnu hinc).toFun X := by
  classical
  by_cases h : nu = mu
  · subst nu
    rw [canonicalForward_self, (canonicalCartan_self_apply mu hmu hinc hd X).1]
    exact TraceCloning.identityChannel_apply X
  · simp only [canonicalForward, dif_neg h]

/-- The total reverse map likewise is the same actual Cartan partial trace. -/
theorem canonicalReverse_eq_cartan_apply (mu nu : Fin d → ℕ) (hmu : Antitone mu)
    (hnu : Antitone nu) (hinc : Antitone (fun i => (nu i : ℝ) - (mu i : ℝ)))
    (hd : 0 < d) (Y : Matrix (IrrepIndex nu) (IrrepIndex nu) ℂ) :
    (canonicalReverse mu nu hmu hnu hinc).toFun Y =
      (canonicalCartanReverse mu nu hmu hnu hinc).toFun Y := by
  classical
  by_cases h : nu = mu
  · subst nu
    rw [canonicalReverse_self, (canonicalCartan_self_apply mu hmu hinc hd Y).2]
    exact TraceCloning.identityChannel_apply Y
  · simp only [canonicalReverse, dif_neg h]

end FreeEntropy.ExteriorRepresentation
