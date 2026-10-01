/-
Copyright (c) 2026 Free Entropy formalization contributors.
See LICENSE and NOTICE in the repository root for license and attribution.
-/

import FreeEntropy.CanonicalOrbit
import FreeEntropy.CanonicalMonomialState
import FreeEntropy.SpecifiedLieCloning
import FreeEntropy.TensorLieIntertwiners

/-! Covariance of the actual Cartan channels from their genuine Lie
intertwiners and physical tensor embeddings. Scalar unitary twists cancel
from the channel formulas. -/
noncomputable section
open Matrix
open scoped BigOperators Kronecker
namespace FreeEntropy.SchurWeyl
set_option backward.isDefEq.respectTransparency false
variable {d n m : ℕ} {A B : Type*} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]

/-- An actual physical embedding identifies its generators by left inverse. -/
theorem restrictedGenerators_eq_of_intertwines
    (R : Matrix.unitaryGroup (Fin d) ℂ →* Matrix A A ℂ)
    (J : Matrix (Fin n → Fin d) A ℂ) (hJ : Jᴴ * J = 1)
    (hJR : ∀ U, physicalRepresentation d n U * J = J * R U)
    (E : LieMatrixCasimir.Generators d A)
    (hE : ∀ i j, (TensorPowers.generators d n).E i j * J = J * E.E i j)
    (i j : Fin d) : (restrictedGenerators R J hJ hJR).E i j = E.E i j := by
  change Jᴴ * (TensorPowers.generators d n).E i j * J = E.E i j
  rw [Matrix.mul_assoc, hE, ← Matrix.mul_assoc, hJ, Matrix.one_mul]

/-- The Lie-to-group bridge also accepts supplied literal generator equations,
so it composes with tensor-product and coordinate isometries. -/
theorem group_intertwiner_of_physical_generators
    (R : Matrix.unitaryGroup (Fin d) ℂ →* Matrix A A ℂ)
    (S : Matrix.unitaryGroup (Fin d) ℂ →* Matrix B B ℂ)
    (J : Matrix (Fin n → Fin d) A ℂ) (K : Matrix (Fin m → Fin d) B ℂ)
    (hn : n = m) (hJ : Jᴴ * J = 1) (hK : Kᴴ * K = 1)
    (hJR : ∀ U, physicalRepresentation d n U * J = J * R U)
    (hKS : ∀ U, physicalRepresentation d m U * K = K * S U)
    (E : LieMatrixCasimir.Generators d A) (F : LieMatrixCasimir.Generators d B)
    (hE : ∀ i j, (TensorPowers.generators d n).E i j * J = J * E.E i j)
    (hF : ∀ i j, (TensorPowers.generators d m).E i j * K = K * F.E i j)
    (V : Matrix B A ℂ) (hV : ∀ i j, V * E.E i j = F.E i j * V)
    (U : Matrix.unitaryGroup (Fin d) ℂ) : V * R U = S U * V := by
  subst m
  apply restricted_group_intertwiner_of_generators R S J K hJ hK hJR hKS V
  intro i j
  rw [restrictedGenerators_eq_of_intertwines R J hJ hJR E hE,
    restrictedGenerators_eq_of_intertwines S K hK hKS F hF]
  exact hV i j

end FreeEntropy.SchurWeyl

namespace FreeEntropy.ExteriorRepresentation
set_option backward.isDefEq.respectTransparency false
variable {d : ℕ}

theorem canonicalPhysicalWeightEmbedding_intertwines (mu : Fin d → ℕ)
    (U : Matrix.unitaryGroup (Fin d) ℂ) :
    SchurWeyl.physicalRepresentation d (tensorDegree mu) U * canonicalPhysicalWeightEmbedding mu =
      canonicalPhysicalWeightEmbedding mu * canonicalWeightRepresentation mu U := by
  let Q := (canonicalWeightCoordinates mu).unitary
  have hQ : Q * Qᴴ = 1 := mul_eq_one_comm.mp (canonicalWeightCoordinates mu).isometry
  change _ * (irrepTensorEmbedding mu * Q) =
    (irrepTensorEmbedding mu * Q) * (Qᴴ * irrepMatrix mu U * Q)
  rw [← Matrix.mul_assoc, irrepTensorEmbedding_intertwines]
  simp only [Matrix.mul_assoc, ← Matrix.mul_assoc Q Qᴴ, hQ, Matrix.one_mul]

end FreeEntropy.ExteriorRepresentation

namespace FreeEntropy.CartanChannel
set_option backward.isDefEq.respectTransparency false
variable {A B C : Type*} [Fintype A] [DecidableEq A]
  [Fintype B] [DecidableEq B] [Fintype C] [DecidableEq C]

theorem phase_conjugation (a : ℂ) (ha : a * star a = 1)
    (Z Y : Matrix C C ℂ) : (a • Z) * Y * (a • Z)ᴴ = Z * Y * Zᴴ := by
  have ha' : star a * a = 1 := by simpa only [mul_comm] using ha
  simp only [Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, ha', one_smul]

/-- A unitary scalar discrepancy in the intertwiner cancels in the forward
channel, as needed for determinant shifts of signed auxiliary weights. -/
theorem sectorMap_covariant_phase (U : Matrix A A ℂ) (W : Matrix B B ℂ)
    (Z : Matrix C C ℂ) (V : Matrix (A × B) C ℂ) (a : ℂ) (ha : a * star a = 1)
    (hU : Uᴴ * U = 1) (hW : Wᴴ * W = 1) (hZ : Z * Zᴴ = 1)
    (hV : (U ⊗ₖ W) * V = V * (a • Z)) (din dout : ℝ) (X : Matrix A A ℂ) :
    sectorMap din dout V (U * X * Uᴴ) = Z * sectorMap din dout V X * Zᴴ := by
  have hphase : (a • Z) * (a • Z)ᴴ = 1 := by
    simpa only [Matrix.mul_one, hZ] using phase_conjugation a ha Z (1 : Matrix C C ℂ)
  simpa only [phase_conjugation a ha] using
    sectorMap_covariant U W (a • Z) V hU hW hphase hV din dout X

theorem reverseMap_covariant_phase (U : Matrix A A ℂ) (W : Matrix B B ℂ)
    (Z : Matrix C C ℂ) (V : Matrix (A × B) C ℂ) (a : ℂ) (ha : a * star a = 1)
    (hW : Wᴴ * W = 1) (hV : (U ⊗ₖ W) * V = V * (a • Z)) (Y : Matrix C C ℂ) :
    reverseMap V (Z * Y * Zᴴ) = U * reverseMap V Y * Uᴴ := by
  simpa only [phase_conjugation a ha] using reverseMap_covariant U W (a • Z) V hW hV Y

end FreeEntropy.CartanChannel
