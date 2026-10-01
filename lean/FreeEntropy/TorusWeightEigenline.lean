/-
Copyright (c) 2026 Free Entropy formalization contributors.
See LICENSE and NOTICE in the repository root for license and attribution.
-/

import FreeEntropy.CyclicHighestRepresentation
import FreeEntropy.OccupationTorus

/-! Distinct integral torus weights are separated by concrete unitary phases.
Consequently a weight occurring at exactly one coordinate has a genuine
one-dimensional simultaneous eigenspace. -/

noncomputable section
open Matrix
open scoped BigOperators

namespace FreeEntropy.TorusWeights

variable {I B G : Type*} [Fintype I] [DecidableEq I]
  [Fintype B] [DecidableEq B]

def character (z : I → ℂ) (a : I → ℕ) : ℂ := ∏ i, z i ^ a i

/-- No bound or common total degree is needed to separate two natural weights. -/
theorem character_separates (a b : I → ℕ) (hab : a ≠ b) :
    ∃ z : I → ℂ, (∀ i, ‖z i‖ = 1) ∧ character z a ≠ character z b := by
  classical
  obtain ⟨i, hi⟩ : ∃ i, a i ≠ b i := by
    by_contra hn
    push_neg at hn
    exact hab (funext hn)
  let n := max (a i) (b i) + 1
  let ζ := Complex.exp (2 * Real.pi * Complex.I / (n : ℕ))
  have hn : n ≠ 0 := by dsimp [n]; omega
  have hζ : IsPrimitiveRoot ζ n := Complex.isPrimitiveRoot_exp _ hn
  let z : I → ℂ := Function.update (fun _ => 1) i ζ
  refine ⟨z, ?_, ?_⟩
  · intro j
    by_cases h : j = i
    · subst j; simpa [z] using hζ.norm'_eq_one hn
    · simp [z, h]
  · have hchar (a : I → ℕ) : character z a = ζ ^ a i := by
      unfold character
      rw [Finset.prod_eq_single i]
      · simp [z]
      · intro j _ hji; simp [z, hji]
      · simp
    rw [hchar, hchar]
    intro h
    exact hi (hζ.pow_inj (by dsimp [n]; omega) (by dsimp [n]; omega) h)

/-- Every vector with the selected joint torus weight is supported on its
actual weight fiber. -/
theorem joint_eigenvector_support (weight : B → I → ℕ) (target : I → ℕ)
    (v : B → ℂ)
    (hv : ∀ z : I → ℂ, (∀ i, ‖z i‖ = 1) →
      (diagonal (fun b => character z (weight b))) *ᵥ v = character z target • v)
    (b : B) (hb : weight b ≠ target) : v b = 0 := by
  obtain ⟨z, hz, hne⟩ := character_separates (weight b) target hb
  have h := congrFun (hv z hz) b
  simp only [Matrix.mulVec_diagonal, Pi.smul_apply, smul_eq_mul] at h
  have hp : (character z (weight b) - character z target) * v b = 0 := by
    rw [sub_mul, h, sub_self]
  exact (mul_eq_zero.mp hp).resolve_left (sub_ne_zero.mpr hne)

/-- A singleton weight fiber gives an actual one-dimensional eigenspace. -/
theorem joint_eigenvector_scalar (weight : B → I → ℕ) (b₀ : B)
    (hweight : ∀ b, weight b = weight b₀ → b = b₀) (v : B → ℂ)
    (hv : ∀ z : I → ℂ, (∀ i, ‖z i‖ = 1) →
      (diagonal (fun b => character z (weight b))) *ᵥ v = character z (weight b₀) • v) :
    v = v b₀ • (Pi.single b₀ (1 : ℂ) : B → ℂ) := by
  classical
  ext b
  by_cases hb : b = b₀
  · subst b; simp
  · have hw : weight b ≠ weight b₀ := fun h => hb (hweight b h)
    simp [Pi.single_apply, hb, joint_eigenvector_support weight (weight b₀) v hv b hw]

def highestVector (b₀ : B) : EuclideanSpace ℂ B := WithLp.toLp 2 ((Pi.single b₀ (1 : ℂ) : B → ℂ))

theorem highestVector_ne_zero (b₀ : B) : highestVector b₀ ≠ 0 := by
  intro h
  have := congrArg (fun v : EuclideanSpace ℂ B => v b₀) h
  simpa [highestVector] using this

/-- Apply the cyclic irreducibility theorem directly to a matrix representation
with an explicitly diagonal torus action and a singleton highest-weight fiber. -/
theorem cyclic_irreducible [Group G] (U : G →* Matrix B B ℂ)
    (hU : ∀ g, (U g)ᴴ * U g = 1)
    (torus : (z : I → ℂ) → (∀ i, ‖z i‖ = 1) → G)
    (weight : B → I → ℕ)
    (hdiag : ∀ z hz, U (torus z hz) = diagonal (fun b => character z (weight b)))
    (b₀ : B) (hweight : ∀ b, weight b = weight b₀ → b = b₀) :
    UnitaryDecomposition.IrreducibleSubspace (UnitaryDecomposition.euclideanRepresentation U)
      (UnitaryDecomposition.cyclicSubspace (UnitaryDecomposition.euclideanRepresentation U)
        (highestVector b₀)) := by
  let T := {z : I → ℂ // ∀ i, ‖z i‖ = 1}
  apply UnitaryDecomposition.cyclicSubspace_irreducible_of_unique_weight
    (UnitaryDecomposition.euclideanRepresentation U)
    (UnitaryDecomposition.euclideanRepresentation_adjoint U hU)
    (fun z : T => torus z.val z.property)
    (fun z : T => character z.val (weight b₀)) (highestVector b₀)
    (highestVector_ne_zero b₀)
  · intro z
    apply PiLp.ext
    intro b
    change (U (torus z.val z.property) *ᵥ (Pi.single b₀ (1 : ℂ) : B → ℂ)) b = _
    rw [hdiag, Matrix.mulVec_diagonal]
    by_cases hb : b = b₀
    · subst b; simp [highestVector]
    · simp [highestVector, Pi.single_apply, hb]
  · intro w hw
    refine ⟨w b₀, ?_⟩
    have hv : (fun b => w b) = w b₀ • (Pi.single b₀ (1 : ℂ) : B → ℂ) :=
      joint_eigenvector_scalar weight b₀ hweight (fun b => w b) (fun z hz => by
        have h := hw (⟨z, hz⟩ : T)
        have hh := congrArg (fun v : EuclideanSpace ℂ B => (fun b => v b)) h
        change U (torus z hz) *ᵥ (fun b => w b) = _ at hh
        rwa [hdiag] at hh)
    apply PiLp.ext
    intro b
    exact congrFun hv b

end FreeEntropy.TorusWeights
