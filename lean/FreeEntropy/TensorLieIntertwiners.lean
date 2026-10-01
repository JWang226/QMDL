/-
Copyright (c) 2026 Free Entropy formalization contributors.
See LICENSE and NOTICE in the repository root for license and attribution.
-/

import FreeEntropy.TensorLieCyclicitySubspace

/-! Rectangular intertwiners of actual physical Lie summands automatically
intertwine the full physical unitary-group action. -/
noncomputable section
open Matrix
namespace FreeEntropy.SchurWeyl
set_option backward.isDefEq.respectTransparency false
variable {d n : ℕ} {A B : Type*} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]

theorem restricted_group_intertwiner_of_generators
    (R : Matrix.unitaryGroup (Fin d) ℂ →* Matrix A A ℂ)
    (S : Matrix.unitaryGroup (Fin d) ℂ →* Matrix B B ℂ)
    (J : Matrix (Fin n → Fin d) A ℂ) (K : Matrix (Fin n → Fin d) B ℂ)
    (hJ : Jᴴ * J = 1) (hK : Kᴴ * K = 1)
    (hJR : ∀ U, physicalRepresentation d n U * J = J * R U)
    (hKS : ∀ U, physicalRepresentation d n U * K = K * S U)
    (F : Matrix B A ℂ)
    (hF : ∀ i j, F * (restrictedGenerators R J hJ hJR).E i j =
      (restrictedGenerators S K hK hKS).E i j * F)
    (U : Matrix.unitaryGroup (Fin d) ℂ) : F * R U = S U * F := by
  let E := TensorPowers.generators d n
  let ER := restrictedGenerators R J hJ hJR
  let ES := restrictedGenerators S K hK hKS
  have hR (i j : Fin d) : E.E i j * J = J * ER.E i j :=
    restrictedGenerators_intertwines R J hJ hJR i j
  have hS (i j : Fin d) : E.E i j * K = K * ES.E i j :=
    restrictedGenerators_intertwines S K hK hKS i j
  have hstar (i j : Fin d) : Jᴴ * E.E i j = ER.E i j * Jᴴ := by
    have h := congrArg Matrix.conjTranspose (hR j i)
    simpa only [Matrix.conjTranspose_mul, E.adjoint, ER.adjoint] using h
  have hLift : TensorCommutant (K * F * Jᴴ) := by
    apply (tensorCommutant_iff_generators _).mpr
    intro i j
    change K * F * Jᴴ * E.E i j = E.E i j * (K * F * Jᴴ)
    calc
      _ = K * (F * ER.E i j) * Jᴴ := by rw [Matrix.mul_assoc, hstar]; simp only [Matrix.mul_assoc]
      _ = K * (ES.E i j * F) * Jᴴ := by rw [hF]
      _ = _ := by rw [← Matrix.mul_assoc K (ES.E i j), ← hS]; simp only [Matrix.mul_assoc]
  have h := congrArg (fun X => Kᴴ * X * J) (hLift U)
  change Kᴴ * (K * F * Jᴴ * physicalRepresentation d n U) * J =
    Kᴴ * (physicalRepresentation d n U * (K * F * Jᴴ)) * J at h
  have hadj := intertwiner_adjoint S K hK hKS U
  simpa only [Matrix.mul_assoc, hJR, ← Matrix.mul_assoc Kᴴ K, ← Matrix.mul_assoc Jᴴ J, hK, hJ,
    Matrix.one_mul, Matrix.mul_one, ← Matrix.mul_assoc Kᴴ (physicalRepresentation d n U),
    hadj] using h

end FreeEntropy.SchurWeyl
