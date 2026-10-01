/-
Copyright (c) 2026 Free Entropy formalization contributors.
See LICENSE and NOTICE in the repository root for license and attribution.
-/

import FreeEntropy.TensorSites
import FreeEntropy.SchurWeylBlocks

/-! Every actual unitary tensor summand carries genuine restricted matrix Lie
generators. The group-to-Lie intertwining is proved by differentiation. -/
noncomputable section
open Matrix
namespace FreeEntropy.SchurWeyl
set_option backward.isDefEq.respectTransparency false
variable {d n : ℕ} {A : Type*} [Fintype A] [DecidableEq A]

theorem differential_intertwines
    (R : Matrix.unitaryGroup (Fin d) ℂ →* Matrix A A ℂ)
    (J : Matrix (Fin n → Fin d) A ℂ) (hJ : Jᴴ * J = 1)
    (hJR : ∀ U, physicalRepresentation d n U * J = J * R U)
    (X : Matrix (Fin d) (Fin d) ℂ) :
    TensorPowers.differential n X * J =
      J * (Jᴴ * TensorPowers.differential n X * J) := by
  have h := (copy_matrixUnit_commutant R J J hJ hJR hJR).differential X
  have he := congrArg (fun M => M * J) h
  simpa only [Matrix.mul_assoc, hJ, Matrix.mul_one] using he.symm

private theorem compressed_product {H : Type*} [Fintype H]
    (J : Matrix H A ℂ) (X Y : Matrix H H ℂ)
    (hY : Y * J = J * (Jᴴ * Y * J)) :
    (Jᴴ * X * J) * (Jᴴ * Y * J) = Jᴴ * (X * Y) * J := by
  calc
    _ = Jᴴ * X * (J * (Jᴴ * Y * J)) := by simp only [Matrix.mul_assoc]
    _ = Jᴴ * X * (Y * J) := by rw [← hY]
    _ = _ := by simp only [Matrix.mul_assoc]

/-- Compression of the explicit physical generators gives an actual
`gl(d)` representation on every genuinely invariant isometric summand. -/
def restrictedGenerators
    (R : Matrix.unitaryGroup (Fin d) ℂ →* Matrix A A ℂ)
    (J : Matrix (Fin n → Fin d) A ℂ) (hJ : Jᴴ * J = 1)
    (hJR : ∀ U, physicalRepresentation d n U * J = J * R U) :
    LieMatrixCasimir.Generators d A where
  E i j := Jᴴ * (TensorPowers.generators d n).E i j * J
  adjoint i j := by
    simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
      (TensorPowers.generators d n).adjoint, Matrix.mul_assoc]
  commutator i j k l := by
    have hE (i j : Fin d) : (TensorPowers.generators d n).E i j * J =
        J * (Jᴴ * (TensorPowers.generators d n).E i j * J) :=
      differential_intertwines R J hJ hJR _
    rw [compressed_product J _ _ (hE k l),
      compressed_product J _ _ (hE i j),
      ← Matrix.sub_mul, ← Matrix.mul_sub, (TensorPowers.generators d n).commutator]
    split_ifs <;> simp [Matrix.mul_sub, Matrix.sub_mul]

theorem restrictedGenerators_intertwines
    (R : Matrix.unitaryGroup (Fin d) ℂ →* Matrix A A ℂ)
    (J : Matrix (Fin n → Fin d) A ℂ) (hJ : Jᴴ * J = 1)
    (hJR : ∀ U, physicalRepresentation d n U * J = J * R U) (i j : Fin d) :
    (TensorPowers.generators d n).E i j * J =
      J * (restrictedGenerators R J hJ hJR).E i j :=
  differential_intertwines R J hJ hJR _

end FreeEntropy.SchurWeyl
