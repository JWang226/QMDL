/-
Copyright (c) 2026 Free Entropy formalization contributors.
See LICENSE and NOTICE in the repository root for license and attribution.
-/

import FreeEntropy.ConstantWeightPhase
import FreeEntropy.TensorPowersPair
import FreeEntropy.SignedAuxiliaryModel
import FreeEntropy.SpecifiedCloningChannels
import FreeEntropy.CanonicalCloning

/-! The actual canonical Cartan channels are covariant under U(d), including
signed auxiliary highest weights. The compensating constant-row representation
is constructed and proved one-dimensional; its unitary phase cancels. -/
noncomputable section
open Matrix
open scoped BigOperators Kronecker
namespace FreeEntropy.ExteriorRepresentation
open CartanLieCloning LieMatrixCasimir CartanChannel
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
variable {d : ℕ}

local instance ci_nonempty (mu : Fin d → ℕ) : Nonempty (IrrepIndex mu) :=
  Fin.pos_iff_nonempty.mp (irrep_dimension_pos mu)

def canonicalPairRepresentation (mu nu : Fin d → ℕ) :=
  pairRepresentation (canonicalWeightRepresentation mu) (canonicalWeightRepresentation nu)

def canonicalPairPhysicalEmbedding (mu nu : Fin d → ℕ) :=
  TensorPowers.pairEmbedding (canonicalPhysicalWeightEmbedding mu) (canonicalPhysicalWeightEmbedding nu)

theorem canonicalPairPhysicalEmbedding_isometry (mu nu : Fin d → ℕ) :
    (canonicalPairPhysicalEmbedding mu nu)ᴴ * canonicalPairPhysicalEmbedding mu nu = 1 :=
  TensorPowers.pairEmbedding_isometry _ _ (canonicalPhysicalWeightEmbedding_isometry mu)
    (canonicalPhysicalWeightEmbedding_isometry nu)

theorem canonicalPairPhysicalEmbedding_intertwines (mu nu : Fin d → ℕ)
    (U : Matrix.unitaryGroup (Fin d) ℂ) :
    SchurWeyl.physicalRepresentation d (tensorDegree mu + tensorDegree nu) U *
      canonicalPairPhysicalEmbedding mu nu =
        canonicalPairPhysicalEmbedding mu nu * canonicalPairRepresentation mu nu U :=
  TensorPowers.pairEmbedding_intertwines _ _ _ _ _
    (canonicalPhysicalWeightEmbedding_intertwines mu U) (canonicalPhysicalWeightEmbedding_intertwines nu U)

theorem canonicalPairPhysicalEmbedding_generators (mu nu : Fin d → ℕ) (i j : Fin d) :
    (TensorPowers.generators d (tensorDegree mu + tensorDegree nu)).E i j *
      canonicalPairPhysicalEmbedding mu nu = canonicalPairPhysicalEmbedding mu nu *
        ((canonicalWeightModel mu).generators.tensor (canonicalWeightModel nu).generators).E i j :=
  TensorPowers.pairEmbedding_generators _ _ _ _ (canonicalPhysicalWeightEmbedding_generators mu)
    (canonicalPhysicalWeightEmbedding_generators nu) i j

/-- A literal Lie intertwiner between equal-degree canonical tensor products
intertwines the full unitary action. -/
theorem canonical_pairs_group_intertwiner (mu omega nu tau : Fin d → ℕ)
    (hdeg : tensorDegree nu + tensorDegree tau = tensorDegree mu + tensorDegree omega)
    (V : Matrix (IrrepIndex mu × IrrepIndex omega) (IrrepIndex nu × IrrepIndex tau) ℂ)
    (hV : ∀ i j, V *
      ((canonicalWeightModel nu).generators.tensor (canonicalWeightModel tau).generators).E i j =
      ((canonicalWeightModel mu).generators.tensor (canonicalWeightModel omega).generators).E i j * V)
    (U : Matrix.unitaryGroup (Fin d) ℂ) :
    V * canonicalPairRepresentation nu tau U = canonicalPairRepresentation mu omega U * V :=
  SchurWeyl.group_intertwiner_of_physical_generators
    (canonicalPairRepresentation nu tau) (canonicalPairRepresentation mu omega)
    (canonicalPairPhysicalEmbedding nu tau) (canonicalPairPhysicalEmbedding mu omega) hdeg
    (canonicalPairPhysicalEmbedding_isometry nu tau) (canonicalPairPhysicalEmbedding_isometry mu omega)
    (canonicalPairPhysicalEmbedding_intertwines nu tau) (canonicalPairPhysicalEmbedding_intertwines mu omega)
    _ _ (canonicalPairPhysicalEmbedding_generators nu tau) (canonicalPairPhysicalEmbedding_generators mu omega)
    V hV U

end FreeEntropy.ExteriorRepresentation

namespace FreeEntropy.LieMatrixCasimir
set_option backward.isDefEq.respectTransparency false
variable {d : ℕ} {A B C : Type*} [Fintype A] [DecidableEq A]
  [Fintype B] [DecidableEq B] [Fintype C] [DecidableEq C]

theorem Generators.tensor_shift (E : Generators d A) (F : Generators d B) (c : ℝ) (i j : Fin d) :
    (E.tensor (F.shift c)).E i j = ((E.tensor F).shift c).E i j := by
  by_cases hij : i = j <;>
    simp [Generators.tensor, Generators.shift, hij, Matrix.kronecker_add,
      Matrix.kronecker_smul, Matrix.one_kronecker_one, add_assoc]

theorem Generators.intertwines_shift_move (E : Generators d A) (F : Generators d B)
    (S : Generators d C) (c : ℝ) (V : Matrix (A × B) C ℂ)
    (hV : ∀ i j, (E.tensor (F.shift (-c))).E i j * V = V * S.E i j)
    (i j : Fin d) : (E.tensor F).E i j * V = V * (S.shift c).E i j := by
  have h := hV i j
  rw [E.tensor_shift F (-c)] at h
  by_cases hij : i = j
  · subst j
    rw [Generators.shift_diagonal] at h ⊢
    simp only [Matrix.add_mul, neg_smul, Matrix.neg_mul, Matrix.smul_mul, Matrix.one_mul] at h
    rw [Matrix.mul_add, Matrix.mul_smul, Matrix.mul_one]
    exact eq_add_of_sub_eq (by simpa only [sub_eq_add_neg] using h)
  · simpa only [Generators.shift_offdiagonal _ _ _ _ hij] using h

end FreeEntropy.LieMatrixCasimir

namespace FreeEntropy.CartanChannel
open LieMatrixCasimir CartanLieCloning
set_option backward.isDefEq.respectTransparency false
variable {d : ℕ} {A B : Type*} [Fintype A] [DecidableEq A]
  [Fintype B] [DecidableEq B] [Nonempty B] [Subsingleton B]

theorem basisEmbedding_shift_generators (S : Generators d A) (T : CyclicWeightModel d B)
    (c : ℝ) (hrow : ∀ i, T.row i = c) (k : B) (i j : Fin d) :
    (S.tensor T.generators).E i j * basisEmbedding k = basisEmbedding k * (S.shift c).E i j := by
  rw [Generators.tensor, Matrix.add_mul,
    basisEmbedding_phase (S.E i j) (1 : Matrix B B ℂ) k,
    basisEmbedding_phase (1 : Matrix A A ℂ) (T.generators.E i j) k,
    T.subsingleton_generators c hrow]
  by_cases hij : i = j
  · subst j
    simp only [ite_true, Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one,
      one_smul, Generators.shift_diagonal, Matrix.mul_add]
    congr 2
    ext a b
    simp [Matrix.smul_apply, Complex.real_smul]
  · simp [hij, Generators.shift_offdiagonal S c i j hij]

end FreeEntropy.CartanChannel

namespace FreeEntropy.ExteriorRepresentation
open CartanLieCloning LieMatrixCasimir CartanChannel
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
variable {d : ℕ}
local instance signed_ci_nonempty (mu : Fin d → ℕ) : Nonempty (IrrepIndex mu) :=
  Fin.pos_iff_nonempty.mp (irrep_dimension_pos mu)

/-- A signed Lie Cartan intertwiner intertwines the actual unitary actions
up to the phase of a constructed one-dimensional polynomial representation. -/
theorem canonical_signed_intertwiner_phase (mu omega nu : Fin d → ℕ)
    (hmu : Antitone mu) (homega : Antitone omega) (hnu : Antitone nu)
    (c : ℕ) (hd : 0 < d) (hbalance : mu + omega = nu + fun _ => c)
    (V : Matrix (IrrepIndex mu × IrrepIndex omega) (IrrepIndex nu) ℂ)
    (hV : ∀ i j, ((canonicalWeightModel mu).generators.tensor
      ((canonicalWeightModel omega).generators.shift (-(c : ℝ)))).E i j * V =
        V * (canonicalWeightModel nu).generators.E i j)
    (U : Matrix.unitaryGroup (Fin d) ℂ) :
    ∃ a : ℂ, a * star a = 1 ∧
      (canonicalWeightRepresentation mu U ⊗ₖ canonicalWeightRepresentation omega U) * V =
        V * (a • canonicalWeightRepresentation nu U) := by
  let tau : Fin d → ℕ := fun _ => c
  let T := canonicalWeightModel tau
  let S := (canonicalWeightModel nu).generators
  let P := (canonicalWeightModel mu).generators.tensor (canonicalWeightModel omega).generators
  letI : Subsingleton (IrrepIndex tau) := constantWeightIndex_subsingleton c hd
  let k : IrrepIndex tau := T.highestBasis
  let B : Matrix (IrrepIndex nu × IrrepIndex tau) (IrrepIndex nu) ℂ := basisEmbedding k
  have hB : Bᴴ * B = 1 := basisEmbedding_isometry k
  have hTrow : ∀ i, T.row i = (c : ℝ) := by
    intro i
    change (canonicalWeightModel tau).row i = (c : ℝ)
    rw [canonicalWeightModel_row tau (fun _ _ _ => le_rfl)]
  have hBE (i j : Fin d) : (S.tensor T.generators).E i j * B = B * (S.shift c).E i j :=
    basisEmbedding_shift_generators S T c hTrow k i j
  have hBstar (i j : Fin d) : Bᴴ * (S.tensor T.generators).E i j = (S.shift c).E i j * Bᴴ := by
    simpa only [Matrix.conjTranspose_mul, Generators.adjoint] using congrArg Matrix.conjTranspose (hBE j i)
  have hVE (i j : Fin d) : P.E i j * V = V * (S.shift c).E i j :=
    Generators.intertwines_shift_move _ _ _ c V hV i j
  have hdegree : tensorDegree nu + tensorDegree tau = tensorDegree mu + tensorDegree omega := by
    rw [tensorDegree_eq_sum nu hnu, tensorDegree_eq_sum tau (fun _ _ _ => le_rfl),
      tensorDegree_eq_sum mu hmu, tensorDegree_eq_sum omega homega]
    have h := congrArg (fun f : Fin d → ℕ => ∑ i, f i) hbalance
    simpa only [Finset.sum_add_distrib, Pi.add_apply] using h.symm
  have hLie (i j : Fin d) : (V * Bᴴ) * (S.tensor T.generators).E i j = P.E i j * (V * Bᴴ) := by
    rw [Matrix.mul_assoc, hBstar, ← Matrix.mul_assoc, ← hVE, Matrix.mul_assoc]
  have hG := canonical_pairs_group_intertwiner mu omega nu tau hdegree (V * Bᴴ) hLie U
  let a : ℂ := canonicalWeightRepresentation tau U k k
  refine ⟨a, subsingleton_unitary_phase _ k (canonicalWeightRepresentation_unitary tau U), ?_⟩
  have hphase : canonicalPairRepresentation nu tau U * B = B * (a • canonicalWeightRepresentation nu U) :=
    basisEmbedding_phase _ _ k
  have h := congrArg (fun X => X * B) hG
  change (V * Bᴴ) * canonicalPairRepresentation nu tau U * B =
    canonicalPairRepresentation mu omega U * (V * Bᴴ) * B at h
  simp only [Matrix.mul_assoc, hphase, ← Matrix.mul_assoc Bᴴ B, hB, Matrix.one_mul] at h
  simpa only [Matrix.mul_one] using h.symm

/-- The exact specified Cartan inclusion used by the cloning estimates has
actual unitary covariance up to a scalar phase, with no covariance premise. -/
theorem specifiedCanonicalCartan_phase (mu nu : Fin d → ℕ)
    (hmu : Antitone mu) (hnu : Antitone nu)
    (hinc : Antitone (fun i => (nu i : ℝ) - (mu i : ℝ))) (hd : 0 < d)
    (U : Matrix.unitaryGroup (Fin d) ℂ) :
    let V := specifiedCartanEmbedding (canonicalWeightModel mu) (canonicalAuxiliaryModel mu nu)
      (canonicalWeightModel nu) (canonicalAuxiliaryModel_hrow mu nu hmu hnu hinc)
    ∃ a : ℂ, a * star a = 1 ∧
      (canonicalWeightRepresentation mu U ⊗ₖ canonicalWeightRepresentation (auxiliaryRow mu nu) U) * V =
        V * (a • canonicalWeightRepresentation nu U) := by
  let V := specifiedCartanEmbedding (canonicalWeightModel mu) (canonicalAuxiliaryModel mu nu)
    (canonicalWeightModel nu) (canonicalAuxiliaryModel_hrow mu nu hmu hnu hinc)
  have hinter := specifiedCartanEmbedding_intertwines (canonicalWeightModel mu)
    (canonicalAuxiliaryModel mu nu) (canonicalWeightModel nu)
    (canonicalAuxiliaryModel_hrow mu nu hmu hnu hinc)
  exact canonical_signed_intertwiner_phase mu (auxiliaryRow mu nu) nu hmu
    (auxiliaryRow_antitone mu nu hinc) hnu (auxiliaryShift mu) hd (auxiliaryRow_balance mu nu)
    V hinter U

end FreeEntropy.ExteriorRepresentation

namespace FreeEntropy.ExteriorRepresentation
open CartanLieCloning CartanChannel
set_option backward.isDefEq.respectTransparency false
variable {d : ℕ}
local instance covariance_ci_nonempty (mu : Fin d → ℕ) : Nonempty (IrrepIndex mu) :=
  Fin.pos_iff_nonempty.mp (irrep_dimension_pos mu)

/-- The constructed forward channel is covariant for every actual unitary
and every matrix input, including a signed dominant row difference. -/
theorem canonicalCartanForward_covariant (mu nu : Fin d → ℕ)
    (hmu : Antitone mu) (hnu : Antitone nu)
    (hinc : Antitone (fun i => (nu i : ℝ) - (mu i : ℝ))) (hd : 0 < d)
    (U : Matrix.unitaryGroup (Fin d) ℂ) (X : Matrix (IrrepIndex mu) (IrrepIndex mu) ℂ) :
    (canonicalCartanForward mu nu hmu hnu hinc).toFun
      (canonicalWeightRepresentation mu U * X * (canonicalWeightRepresentation mu U)ᴴ) =
      canonicalWeightRepresentation nu U * (canonicalCartanForward mu nu hmu hnu hinc).toFun X *
        (canonicalWeightRepresentation nu U)ᴴ := by
  obtain ⟨a, ha, hV⟩ := specifiedCanonicalCartan_phase mu nu hmu hnu hinc hd U
  simpa only [canonicalCartanForward, specifiedForward, cartanChannel_apply] using
    sectorMap_covariant_phase (canonicalWeightRepresentation mu U)
      (canonicalWeightRepresentation (auxiliaryRow mu nu) U) (canonicalWeightRepresentation nu U)
      _ a ha (canonicalWeightRepresentation_unitary mu U)
      (canonicalWeightRepresentation_unitary (auxiliaryRow mu nu) U)
      (mul_eq_one_comm.mp (canonicalWeightRepresentation_unitary nu U)) hV
      (Fintype.card (IrrepIndex mu)) (Fintype.card (IrrepIndex nu)) X

/-- The constructed reverse channel has the corresponding exact covariance. -/
theorem canonicalCartanReverse_covariant (mu nu : Fin d → ℕ)
    (hmu : Antitone mu) (hnu : Antitone nu)
    (hinc : Antitone (fun i => (nu i : ℝ) - (mu i : ℝ))) (hd : 0 < d)
    (U : Matrix.unitaryGroup (Fin d) ℂ) (Y : Matrix (IrrepIndex nu) (IrrepIndex nu) ℂ) :
    (canonicalCartanReverse mu nu hmu hnu hinc).toFun
      (canonicalWeightRepresentation nu U * Y * (canonicalWeightRepresentation nu U)ᴴ) =
      canonicalWeightRepresentation mu U * (canonicalCartanReverse mu nu hmu hnu hinc).toFun Y *
        (canonicalWeightRepresentation mu U)ᴴ := by
  obtain ⟨a, ha, hV⟩ := specifiedCanonicalCartan_phase mu nu hmu hnu hinc hd U
  simpa only [canonicalCartanReverse, specifiedReverse, reverseChannel_apply, reverseMap] using
    reverseMap_covariant_phase (canonicalWeightRepresentation mu U)
      (canonicalWeightRepresentation (auxiliaryRow mu nu) U) (canonicalWeightRepresentation nu U)
      _ a ha (canonicalWeightRepresentation_unitary (auxiliaryRow mu nu) U) hV Y

end FreeEntropy.ExteriorRepresentation
