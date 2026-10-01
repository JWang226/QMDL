/-
Copyright (c) 2026 Free Entropy formalization contributors.
See LICENSE and NOTICE in the repository root for license and attribution.
-/

import FreeEntropy.ScalarCommutantIrreducible
import Mathlib.RepresentationTheory.Semisimple
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule

/-! Invariant subspaces and their genuine orthogonal complements for a
finite-dimensional unitary representation. -/

noncomputable section
open Matrix
open scoped ComplexInnerProductSpace

namespace FreeEntropy.UnitaryDecomposition
set_option linter.unusedSectionVars false

variable {G E : Type*} [Group G] [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E]

def Invariant (ρ : Representation ℂ G E) (K : Submodule ℂ E) : Prop :=
  ∀ g x, x ∈ K → ρ g x ∈ K

theorem invariant_bot (ρ : Representation ℂ G E) : Invariant ρ ⊥ := by
  intro g x hx
  have hx0 : x = 0 := hx
  simp [hx0]

theorem invariant_top (ρ : Representation ℂ G E) : Invariant ρ ⊤ := fun _ _ _ => trivial

theorem invariant_inf {ρ : Representation ℂ G E} {K L : Submodule ℂ E}
    (hK : Invariant ρ K) (hL : Invariant ρ L) : Invariant ρ (K ⊓ L) :=
  fun g x hx => ⟨hK g x hx.1, hL g x hx.2⟩

/-- Orthogonal complements are invariant because the group inverse is the adjoint. -/
theorem invariant_orthogonal (ρ : Representation ℂ G E)
    (hstar : ∀ g, (ρ g).adjoint = ρ g⁻¹) {K : Submodule ℂ E}
    (hK : Invariant ρ K) : Invariant ρ Kᗮ := by
  intro g x hx y hy
  rw [← LinearMap.adjoint_inner_left, hstar]
  exact hx _ (hK g⁻¹ y hy)

/-- The actual orthogonal projection onto an invariant subspace commutes
with the representation. -/
theorem projection_commutes (ρ : Representation ℂ G E)
    (hstar : ∀ g, (ρ g).adjoint = ρ g⁻¹) {K : Submodule ℂ E}
    (hK : Invariant ρ K) (g : G) (x : E) :
    K.starProjection (ρ g x) = ρ g (K.starProjection x) := by
  apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero
  · exact hK g _ (K.starProjection_apply_mem x)
  · intro y hy
    rw [← map_sub, ← LinearMap.adjoint_inner_right, hstar]
    exact K.starProjection_inner_eq_zero x _ (hK g⁻¹ y hy)

/-- The true restricted representation on the invariant Hilbert subspace. -/
def restriction (ρ : Representation ℂ G E) (K : Submodule ℂ E) (hK : Invariant ρ K) :
    Representation ℂ G K :=
  (Subrepresentation.mk K (fun g _ hx => hK g _ hx)).toRepresentation

@[simp] theorem restriction_apply (ρ : Representation ℂ G E) (K : Submodule ℂ E)
    (hK : Invariant ρ K) (g : G) (x : K) :
    ((restriction ρ K hK g x : K) : E) = ρ g (x : E) := rfl

/-- Invariant irreducibility expressed inside one fixed ambient Hilbert space. -/
structure IrreducibleSubspace (ρ : Representation ℂ G E) (K : Submodule ℂ E) : Prop where
  invariant : Invariant ρ K
  ne_bot : K ≠ ⊥
  minimal : ∀ L : Submodule ℂ E, Invariant ρ L → L ≤ K → L = ⊥ ∨ L = K

/-- Every nonzero invariant subspace contains an actual minimal nonzero
invariant subspace, by minimization of the positive finite dimension. -/
theorem exists_irreducible_le (ρ : Representation ℂ G E) (K : Submodule ℂ E)
    (hK : Invariant ρ K) (hK0 : K ≠ ⊥) :
    ∃ L : Submodule ℂ E, L ≤ K ∧ IrreducibleSubspace ρ L := by
  classical
  let P : ℕ → Prop := fun n => ∃ L : Submodule ℂ E,
    Invariant ρ L ∧ L ≠ ⊥ ∧ L ≤ K ∧ Module.finrank ℂ L = n
  have hex : ∃ n, P n := ⟨Module.finrank ℂ K, K, hK, hK0, le_rfl, rfl⟩
  obtain ⟨L, hL, hL0, hLK, hdim⟩ := Nat.find_spec hex
  refine ⟨L, hLK, hL, hL0, ?_⟩
  intro J hJ hJL
  by_cases hJ0 : J = ⊥
  · exact Or.inl hJ0
  · right
    have hmin : Nat.find hex ≤ Module.finrank ℂ J :=
      Nat.find_min' hex ⟨J, hJ, hJ0, hJL.trans hLK, rfl⟩
    apply Submodule.eq_of_le_of_finrank_eq hJL
    exact le_antisymm (Submodule.finrank_mono hJL) (by simpa [hdim] using hmin)

/-- Ambient minimality is actual irreducibility of the restricted representation. -/
theorem IrreducibleSubspace.isIrreducible {ρ : Representation ℂ G E} {K : Submodule ℂ E}
    (hK : IrreducibleSubspace ρ K) :
    Representation.IsIrreducible (restriction ρ K hK.invariant) := by
  letI : Nontrivial K := Submodule.nontrivial_iff_ne_bot.mpr hK.ne_bot
  haveI : Nontrivial (Subrepresentation (restriction ρ K hK.invariant)) := by
    refine ⟨⟨⊥, ⊤, ?_⟩⟩
    intro he
    exact bot_ne_top (congrArg Subrepresentation.toSubmodule he :
      (⊥ : Submodule ℂ K) = ⊤)
  refine ⟨fun J => ?_⟩
  let L : Submodule ℂ E := J.toSubmodule.map K.subtype
  have hL : Invariant ρ L := by
    intro g x hx
    obtain ⟨y, hy, rfl⟩ := hx
    exact ⟨restriction ρ K hK.invariant g y, J.apply_mem_toSubmodule g hy, rfl⟩
  have hLK : L ≤ K := by
    rintro x ⟨y, _, rfl⟩
    exact y.property
  rcases hK.minimal L hL hLK with hzero | heq
  · left
    apply Subrepresentation.toSubmodule_injective
    apply le_antisymm ?_ bot_le
    intro x hx
    have hm : (x : E) ∈ L := ⟨x, hx, rfl⟩
    rw [hzero] at hm
    change x = 0
    exact Subtype.ext hm
  · right
    apply Subrepresentation.toSubmodule_injective
    apply top_unique
    intro x _
    have hm : (x : E) ∈ L := heq.symm ▸ x.property
    obtain ⟨y, hy, hyx⟩ := hm
    have he : y = x := Subtype.ext hyx
    simpa only [he] using hy

section Matrices
variable {H : Type*} [Fintype H] [DecidableEq H]

/-- The given matrix representation on its actual Euclidean Hilbert space. -/
def euclideanRepresentation (U : G →* Matrix H H ℂ) :
    Representation ℂ G (EuclideanSpace ℂ H) where
  toFun g := Matrix.toEuclideanLin (U g)
  map_one' := by
    apply LinearMap.ext
    intro x
    simp
  map_mul' g h := by
    apply LinearMap.ext
    intro x
    simp only [map_mul, Module.End.mul_apply, Matrix.toLpLin_apply, Matrix.mulVec_mulVec]

theorem euclideanRepresentation_adjoint (U : G →* Matrix H H ℂ)
    (hU : ∀ g, (U g)ᴴ * U g = 1) (g : G) :
    (euclideanRepresentation U g).adjoint = euclideanRepresentation U g⁻¹ := by
  change (Matrix.toEuclideanLin (U g)).adjoint = Matrix.toEuclideanLin (U g⁻¹)
  rw [← Matrix.toEuclideanLin_conjTranspose_eq_adjoint,
    Twirling.inverse_eq_conjTranspose U hU]

end Matrices
end FreeEntropy.UnitaryDecomposition
