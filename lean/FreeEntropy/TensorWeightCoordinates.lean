/-
Copyright (c) 2026 Free Entropy formalization contributors.
See LICENSE and NOTICE in the repository root for license and attribution.
-/

import FreeEntropy.TensorWeightBasis
import FreeEntropy.CasimirCentral

/-! Unitary changes to the constructed joint weight basis preserve the
actual Lie relations and cyclic highest-vector data. -/
noncomputable section
open Matrix

namespace FreeEntropy.LieMatrixCasimir
set_option backward.isDefEq.respectTransparency false
variable {d : ℕ} {A : Type*} [Fintype A] [DecidableEq A]

/-- Actual change of orthonormal coordinates for a matrix Lie action. -/
def Generators.unitaryConjugate (R : Generators d A) (W : Matrix A A ℂ) (hW : Wᴴ * W = 1) :
    Generators d A where
  E i j := Wᴴ * R.E i j * W
  adjoint i j := by simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
    R.adjoint, Matrix.mul_assoc]
  commutator i j k l := by
    have hWW : W * Wᴴ = 1 := mul_eq_one_comm.mp hW
    have hp (X Y : Matrix A A ℂ) :
        (Wᴴ * X * W) * (Wᴴ * Y * W) = Wᴴ * (X * Y) * W := by
      simp only [Matrix.mul_assoc, ← Matrix.mul_assoc W Wᴴ, hWW, Matrix.one_mul]
    rw [hp, hp, ← Matrix.sub_mul, ← Matrix.mul_sub, R.commutator]
    split_ifs <;> simp [Matrix.mul_sub, Matrix.sub_mul]

theorem Generators.unitaryConjugate_word (R : Generators d A)
    (W : Matrix A A ℂ) (hW : Wᴴ * W = 1) (w : List (Fin d × Fin d)) :
    LiePBW.word (R.unitaryConjugate W hW) w = Wᴴ * LiePBW.word R w * W := by
  have hWW : W * Wᴴ = 1 := mul_eq_one_comm.mp hW
  induction w with
  | nil => simpa [LiePBW.word_nil] using hW.symm
  | cons a w ih =>
    rw [LiePBW.word_cons, LiePBW.word_cons, ih]
    change (Wᴴ * R.E a.1 a.2 * W) * (Wᴴ * LiePBW.word R w * W) = _
    simp only [Matrix.mul_assoc, ← Matrix.mul_assoc W Wᴴ, hWW, Matrix.one_mul]

theorem Generators.unitaryConjugate_action (R : Generators d A)
    (W : Matrix A A ℂ) (hW : Wᴴ * W = 1) (i j : Fin d) (v : A → ℂ) :
    (R.unitaryConjugate W hW).E i j *ᵥ (Wᴴ *ᵥ v) = Wᴴ *ᵥ (R.E i j *ᵥ v) := by
  have hWW : W * Wᴴ = 1 := mul_eq_one_comm.mp hW
  change (Wᴴ * R.E i j * W) *ᵥ (Wᴴ *ᵥ v) = _
  simp only [Matrix.mulVec_mulVec, Matrix.mul_assoc, hWW, Matrix.mul_one]

/-- Lie cyclicity is preserved by the actual orthonormal change of basis. -/
theorem Generators.unitaryConjugate_cyclic (R : Generators d A)
    (W : Matrix A A ℂ) (hW : Wᴴ * W = 1) (v : A → ℂ)
    (hv : LiePBW.cyclicSpan R v = ⊤) :
    LiePBW.cyclicSpan (R.unitaryConjugate W hW) (Wᴴ *ᵥ v) = ⊤ := by
  let F := R.unitaryConjugate W hW
  have hWW : W * Wᴴ = 1 := mul_eq_one_comm.mp hW
  have hm (y : A → ℂ) (hy : y ∈ LiePBW.cyclicSpan R v) :
      Wᴴ *ᵥ y ∈ LiePBW.cyclicSpan F (Wᴴ *ᵥ v) := by
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨w, rfl⟩ := hy
      apply Submodule.subset_span
      refine ⟨w, ?_⟩
      rw [R.unitaryConjugate_word W hW]
      simp only [Matrix.mulVec_mulVec, Matrix.mul_assoc, hWW, Matrix.mul_one]
    | zero => simp
    | add x y hx hy ihx ihy =>
      simpa only [Matrix.mulVec_add] using (LiePBW.cyclicSpan F (Wᴴ *ᵥ v)).add_mem ihx ihy
    | smul c x hx ih =>
      simpa only [Matrix.mulVec_smul] using (LiePBW.cyclicSpan F (Wᴴ *ᵥ v)).smul_mem c ih
  apply top_unique
  intro x _
  have hx := hm (W *ᵥ x) (by rw [hv]; trivial)
  simpa only [Matrix.mulVec_mulVec, hW, Matrix.one_mulVec] using hx

/-- The vector and one-column matrix versions of Lie cyclicity agree. -/
theorem Generators.column_cyclic_of_vector (R : Generators d A) (v : A → ℂ)
    (hv : LiePBW.cyclicSpan R v = ⊤) :
    R.cyclicSpan (fun a (_ : Unit) => v a) = ⊤ := by
  let col : (A → ℂ) →ₗ[ℂ] Matrix A Unit ℂ :=
    { toFun := fun x a _ => x a
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hm (x : A → ℂ) (hx : x ∈ LiePBW.cyclicSpan R v) : col x ∈ R.cyclicSpan (col v) := by
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨w, rfl⟩ := hx
      apply Submodule.subset_span
      exact ⟨w, rfl⟩
    | zero => simp
    | add x y hx hy ihx ihy => simpa only [map_add] using (R.cyclicSpan (col v)).add_mem ihx ihy
    | smul c x hx ih => simpa only [map_smul] using (R.cyclicSpan (col v)).smul_mem c ih
  apply top_unique
  intro X _
  have h := hm (fun a => X a ()) (by rw [hv]; trivial)
  exact h

end FreeEntropy.LieMatrixCasimir

namespace FreeEntropy.SchurWeyl
open Occupation
set_option backward.isDefEq.respectTransparency false
variable {d n : ℕ}

/-- Actual sector Lie generators in the proved simultaneous weight basis. -/
def sectorWeightGenerators (i : Sector d n) :=
  (sectorGenerators i).unitaryConjugate (sectorWeightUnitary i) (sectorWeightUnitary_isometry i)

theorem sectorWeightGenerators_diagonal (i : Sector d n) (j : Fin d) :
    (sectorWeightGenerators i).E j j =
      Matrix.diagonal (fun a => ((sectorWeight i a).val j : ℂ)) :=
  sectorWeightUnitary_diagonal i j

/-- The constructed weight coordinates retain an actual dominant highest
vector and actual full Lie cyclicity. -/
theorem exists_sector_weight_highest (i : Sector d n) :
    ∃ a : Occupation d n, ∃ v : SectorSpace d n i → ℂ,
      v ≠ 0 ∧ Antitone a.val ∧
      (∀ j, (sectorWeightGenerators i).E j j *ᵥ v = (a.val j : ℂ) • v) ∧
      (∀ j k, j < k → (sectorWeightGenerators i).E j k *ᵥ v = 0) ∧
      LiePBW.cyclicSpan (sectorWeightGenerators i) v = ⊤ := by
  obtain ⟨a, v, hv, hdom, hweight, hraise, hcyclic⟩ := exists_sector_highest i
  let W := sectorWeightUnitary i
  have hv' : Wᴴ *ᵥ v ≠ 0 := by
    intro h
    have hh := congrArg (fun x => W *ᵥ x) h
    apply hv
    simpa only [Matrix.mulVec_mulVec, W, sectorWeightUnitary_coisometry,
      Matrix.one_mulVec, Matrix.mulVec_zero] using hh
  refine ⟨a, Wᴴ *ᵥ v, hv', hdom, ?_, ?_,
    (sectorGenerators i).unitaryConjugate_cyclic W (sectorWeightUnitary_isometry i) v hcyclic⟩
  · intro j
    change ((sectorGenerators i).unitaryConjugate W (sectorWeightUnitary_isometry i)).E j j *ᵥ (Wᴴ *ᵥ v) = _
    rw [LieMatrixCasimir.Generators.unitaryConjugate_action, hweight, Matrix.mulVec_smul]
  · intro j k hjk
    change ((sectorGenerators i).unitaryConjugate W (sectorWeightUnitary_isometry i)).E j k *ᵥ (Wᴴ *ᵥ v) = _
    rw [LieMatrixCasimir.Generators.unitaryConjugate_action, hraise j k hjk, Matrix.mulVec_zero]

end FreeEntropy.SchurWeyl
