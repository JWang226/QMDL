/-
Copyright (c) 2026 Free Entropy formalization contributors.
See LICENSE and NOTICE in the repository root for license and attribution.
-/

import FreeEntropy.LieHighestExistence
import FreeEntropy.TensorWeightCoordinates
import FreeEntropy.CartanLieCloning

/-! Actual joint weight coordinates and highest-weight model for a genuine
finite irreducible unitary Lie module. The only irreducibility property used
is cyclicity of each nonzero vector; actual restrictions prove this property. -/
noncomputable section
open Matrix
namespace FreeEntropy.LieMatrixCasimir
set_option backward.isDefEq.respectTransparency false
variable {d : ℕ} {A : Type*} [Fintype A] [DecidableEq A] [Nonempty A]

structure WeightCoordinates (R : Generators d A) where
  model : CartanLieCloning.CyclicWeightModel d A
  unitary : Matrix A A ℂ
  isometry : unitaryᴴ * unitary = 1
  generators : ∀ i j, model.generators.E i j = unitaryᴴ * R.E i j * unitary

/-- Construct all weight-model fields from the actual Lie action and its
proved irreducibility, including the root-cone coefficients. -/
theorem Generators.exists_weightCoordinates (R : Generators d A)
    (hcyclic : ∀ v : A → ℂ, v ≠ 0 → LiePBW.cyclicSpan R v = ⊤) :
    Nonempty (WeightCoordinates R) := by
  classical
  obtain ⟨b, χ, hb⟩ := R.exists_real_jointBasis
  let W : Matrix A A ℂ := fun a c => b c a
  have hW : Wᴴ * W = 1 := by
    ext a c
    have h := b.inner_eq_ite a c
    simpa only [W, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Matrix.one_apply, PiLp.inner_apply, RCLike.inner_apply', RCLike.star_def] using h
  have hWW : W * Wᴴ = 1 := mul_eq_one_comm.mp hW
  let F := R.unitaryConjugate W hW
  have hdiag (j : Fin d) : F.E j j = WeightSectors.weightDiagonal χ j := by
    have h : R.E j j * W = W * Matrix.diagonal (fun a => (χ a j : ℂ)) := by
      ext a c
      rw [Matrix.mul_diagonal]
      have hc := congrFun (hb c j) a
      simpa only [Matrix.mul_apply, W, Matrix.mulVec, dotProduct,
        Pi.smul_apply, Complex.real_smul, smul_eq_mul, mul_comm] using hc
    change Wᴴ * R.E j j * W = _
    rw [Matrix.mul_assoc, h, ← Matrix.mul_assoc, hW, Matrix.one_mul]
    rfl
  obtain ⟨lam, v, hv, hdom, hw, hr⟩ := F.exists_highest
  have hc : LiePBW.cyclicSpan F v = ⊤ := by
    have hWv : W *ᵥ v ≠ 0 := by
      intro h
      have hh := congrArg (fun x => Wᴴ *ᵥ x) h
      exact hv (by simpa only [Matrix.mulVec_mulVec, hW, Matrix.one_mulVec, Matrix.mulVec_zero] using hh)
    have h := R.unitaryConjugate_cyclic W hW (W *ᵥ v) (hcyclic _ hWv)
    simpa only [Matrix.mulVec_mulVec, hW, Matrix.one_mulVec] using h
  have hcone (a : A) : ∃ c : Fin (d - 1) → ℕ, lam - χ a = CasimirWeights.offset c := by
    apply LiePBW.weight_in_root_cone F lam (χ a) v (Pi.single a (1 : ℂ)) hw hr
    · rw [hc]; trivial
    · intro h
      have hh := congrFun h a
      simp at hh
    · intro j
      rw [hdiag]
      ext k
      by_cases h : k = a
      · subst k; simp [WeightSectors.weightDiagonal]
      · simp [WeightSectors.weightDiagonal, Matrix.mulVec_diagonal, h]
  let M : CartanLieCloning.CyclicWeightModel d A :=
    { generators := F
      row := lam
      weight := χ
      highest := fun a _ => v a
      diagonal := hdiag
      highest_weight := fun j => by ext a u; exact congrFun (hw j) a
      highest_raise := fun j k hjk => by ext a u; exact congrFun (hr j k hjk) a
      cyclic := F.column_cyclic_of_vector v hc
      dominant := fun j => hdom (show CasimirWeights.left j ≤ CasimirWeights.right j by
        change j.val ≤ j.val + 1; omega)
      weightCoeff := fun a => (hcone a).choose
      weight_cone := fun a => (hcone a).choose_spec }
  exact ⟨M, W, hW, fun _ _ => rfl⟩

/-- Chosen actual weight coordinates, built from the preceding existence proof. -/
def Generators.weightCoordinates (R : Generators d A)
    (hcyclic : ∀ v : A → ℂ, v ≠ 0 → LiePBW.cyclicSpan R v = ⊤) : WeightCoordinates R :=
  (R.exists_weightCoordinates hcyclic).some

end FreeEntropy.LieMatrixCasimir
