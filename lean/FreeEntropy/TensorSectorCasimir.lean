/-
Copyright (c) 2026 Free Entropy formalization contributors.
See LICENSE and NOTICE in the repository root for license and attribution.
-/

import FreeEntropy.TensorLieCyclicityPhysical
import FreeEntropy.CasimirCentral

/-! Actual Casimir eigenvalues on the constructed physical sectors. The
highest weight, Lie generators and cyclicity are all already constructed. -/
noncomputable section
open Matrix
namespace FreeEntropy.LieMatrixCasimir
set_option backward.isDefEq.respectTransparency false
variable {d : ℕ} {H : Type*} [Fintype H] [DecidableEq H]

theorem Generators.casimir_scalar_of_vector_cyclic (R : Generators d H)
    (lam : Fin d → ℝ) (v : H → ℂ)
    (hweight : ∀ i, R.E i i *ᵥ v = lam i • v)
    (hraise : ∀ i j, i < j → R.E i j *ᵥ v = 0)
    (hcyclic : LiePBW.cyclicSpan R v = ⊤) :
    R.casimir = CasimirWeights.casimir lam • (1 : Matrix H H ℂ) := by
  let P : Matrix H Unit ℂ := fun h _ => v h
  have hPw (i : Fin d) : R.E i i * P = lam i • P := by
    ext h u
    exact congrFun (hweight i) h
  have hPr (i j : Fin d) (hij : i < j) : R.E i j * P = 0 := by
    ext h u
    exact congrFun (hraise i j hij) h
  have hv : R.casimir *ᵥ v = CasimirWeights.casimir lam • v := by
    have h := R.casimir_on_highest P lam hPw hPr
    exact congrArg (fun M : Matrix H Unit ℂ => fun i => M i ()) h
  have hall (x : H → ℂ) (hx : x ∈ LiePBW.cyclicSpan R v) :
      R.casimir *ᵥ x = CasimirWeights.casimir lam • x := by
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨w, rfl⟩ := hx
      change R.casimir *ᵥ (R.wordMatrix w *ᵥ v) = _
      rw [Matrix.mulVec_mulVec, R.casimir_commutes_word,
        ← Matrix.mulVec_mulVec, hv, Matrix.mulVec_smul]
      rfl
    | zero => simp
    | add x y hx hy hx' hy' => simp [Matrix.mulVec_add, hx', hy', smul_add]
    | smul c x hx hx' => simp [Matrix.mulVec_smul, hx', smul_comm (CasimirWeights.casimir lam) c]
  apply (Matrix.toLinAlgEquiv' : Matrix H H ℂ ≃ₐ[ℂ] Module.End ℂ (H → ℂ)).injective
  apply LinearMap.ext
  intro x
  change R.casimir *ᵥ x = (CasimirWeights.casimir lam • (1 : Matrix H H ℂ)) *ᵥ x
  rw [Matrix.smul_mulVec, Matrix.one_mulVec]
  exact hall x (by rw [hcyclic]; trivial)

end FreeEntropy.LieMatrixCasimir

namespace FreeEntropy.SchurWeyl
variable {d n : ℕ}

/-- Every actual physical irreducible block has the prescribed scalar
Casimir at an actual dominant partition of the tensor degree. -/
theorem physical_sector_casimir (i : Sector d n) :
    ∃ a : Occupation.Occupation d n, Antitone a.val ∧
      (sectorGenerators i).casimir = CasimirWeights.casimir (fun k => (a.val k : ℝ)) •
        (1 : Matrix (SectorSpace d n i) (SectorSpace d n i) ℂ) := by
  obtain ⟨a, v, _, hdom, hweight, hraise, hcyclic⟩ := exists_sector_highest i
  refine ⟨a, hdom, ?_⟩
  apply (sectorGenerators i).casimir_scalar_of_vector_cyclic (fun k => (a.val k : ℝ)) v
    (fun k => by simpa using hweight k) hraise hcyclic

end FreeEntropy.SchurWeyl
