/-
Copyright (c) 2026 Free Entropy formalization contributors.
See LICENSE and NOTICE in the repository root for license and attribution.
-/

import FreeEntropy.UnitaryDecompositionBasic

/-! Every finite-dimensional unitary representation has a complete finite
orthogonal family of genuine irreducible invariant subspaces. -/

noncomputable section
open scoped ComplexInnerProductSpace

namespace FreeEntropy.UnitaryDecomposition
set_option linter.unusedSectionVars false

variable {G E : Type*} [Group G] [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E]

def Orthogonal (K L : Submodule ℂ E) : Prop := ∀ x ∈ K, ∀ y ∈ L, ⟪x, y⟫ = 0

theorem orthogonal_symm {K L : Submodule ℂ E} (h : Orthogonal K L) : Orthogonal L K := by
  intro x hx y hy
  exact inner_eq_zero_symm.mp (h y hy x hx)

theorem orthogonal_of_le_complement {K L : Submodule ℂ E} (h : L ≤ Kᗮ) :
    Orthogonal K L := fun x hx _ hy => h hy x hx

/-- Decompose an arbitrary invariant subspace, not merely the ambient top.
The induction strictly reduces the actual finite dimension of the remaining
orthogonal complement at each step. -/
theorem exists_orthogonal_irreducible_family (ρ : Representation ℂ G E)
    (hstar : ∀ g, (ρ g).adjoint = ρ g⁻¹) (K : Submodule ℂ E) (hK : Invariant ρ K) :
    ∃ s : Finset (Submodule ℂ E),
      (∀ L ∈ s, IrreducibleSubspace ρ L) ∧
      (∀ L ∈ s, ∀ J ∈ s, L ≠ J → Orthogonal L J) ∧ s.sup id = K := by
  classical
  generalize hdim : Module.finrank ℂ K = N
  induction N using Nat.strong_induction_on generalizing K with
  | h N ih =>
    by_cases hzero : K = ⊥
    · subst K
      exact ⟨∅, by simp, by simp, by simp⟩
    obtain ⟨L, hLK, hL⟩ := exists_irreducible_le ρ K hK hzero
    let J : Submodule ℂ E := Lᗮ ⊓ K
    have hJ : Invariant ρ J := invariant_inf (invariant_orthogonal ρ hstar hL.invariant) hK
    have hdimJ : Module.finrank ℂ J < N := by
      have he := Submodule.finrank_add_inf_finrank_orthogonal hLK
      have hp : 1 ≤ Module.finrank ℂ L := Submodule.one_le_finrank_iff.mpr hL.ne_bot
      change Module.finrank ℂ L + Module.finrank ℂ J = Module.finrank ℂ K at he
      omega
    obtain ⟨s, hs, hortho, hsup⟩ := ih (Module.finrank ℂ J) hdimJ J hJ rfl
    have hsJ (A : Submodule ℂ E) (hA : A ∈ s) : A ≤ J := by
      rw [← hsup]
      exact Finset.le_sup (f := id) hA
    have hLA (A : Submodule ℂ E) (hA : A ∈ s) : Orthogonal L A :=
      orthogonal_of_le_complement ((hsJ A hA).trans inf_le_left)
    refine ⟨insert L s, ?_, ?_, ?_⟩
    · intro A hA
      rcases Finset.mem_insert.mp hA with rfl | hA
      · exact hL
      · exact hs A hA
    · intro A hA B hB hne
      by_cases hAL : A = L
      · subst A
        exact hLA B ((Finset.mem_insert.mp hB).resolve_left hne.symm)
      have hAs : A ∈ s := (Finset.mem_insert.mp hA).resolve_left hAL
      by_cases hBL : B = L
      · subst B
        exact orthogonal_symm (hLA A hAs)
      exact hortho A hAs B ((Finset.mem_insert.mp hB).resolve_left hBL) hne
    · rw [Finset.sup_insert, hsup]
      exact Submodule.sup_orthogonal_inf_of_hasOrthogonalProjection hLK

/-- Every unitary representation admits a complete orthogonal irreducible
decomposition; no decomposition or representation-existence premise is used. -/
theorem exists_complete_orthogonal_family (ρ : Representation ℂ G E)
    (hstar : ∀ g, (ρ g).adjoint = ρ g⁻¹) :
    ∃ s : Finset (Submodule ℂ E),
      (∀ L ∈ s, IrreducibleSubspace ρ L) ∧
      (∀ L ∈ s, ∀ J ∈ s, L ≠ J → Orthogonal L J) ∧ s.sup id = ⊤ :=
  exists_orthogonal_irreducible_family ρ hstar ⊤ (invariant_top ρ)

theorem sum_projections_eq_identity (s : Finset (Submodule ℂ E))
    (horth : ∀ L ∈ s, ∀ J ∈ s, L ≠ J → Orthogonal L J) (hspan : s.sup id = ⊤)
    (x : E) : (∑ L : s, L.val.starProjection x) = x := by
  classical
  have hfamily : OrthogonalFamily ℂ (fun L : s => L.val) (fun L => L.val.subtypeₗᵢ) := by
    apply OrthogonalFamily.of_pairwise
    intro L J hne
    apply Submodule.isOrtho_iff_inner_eq.mpr
    exact horth L.val L.property J.val J.property (fun h => hne (Subtype.ext h))
  have htop : (⨆ L : s, L.val) = (⊤ : Submodule ℂ E) := by
    simpa only [Finset.sup_eq_iSup, iSup_subtype] using hspan
  exact hfamily.sum_projection_of_mem_iSup x (htop.symm ▸ Submodule.mem_top)

end FreeEntropy.UnitaryDecomposition
