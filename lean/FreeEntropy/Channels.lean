/-
Copyright (c) 2026 Free Entropy formalization contributors.
See LICENSE and NOTICE in the repository root for license and attribution.
-/

import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Order
import Mathlib.LinearAlgebra.Complex.Module

/-!
# Concrete finite-dimensional Kraus channels

The core Kraus/amplification proofs are adapted from the existing local project
`Cloning-github/formalization/Cloning/Channels.lean` (namespace `Cloning.Channels`).
That source was read without modification; this file is independently compiled
against the dependencies pinned by the FreeEntropy project.

Unlike the abstract fidelity interfaces elsewhere, these statements concern
actual complex matrices. Complete positivity is proved at every finite matrix
amplification. The remaining Cartan-specific input is the representation
theoretic construction of the Kraus operators and their normalization.
-/

open scoped BigOperators Matrix Kronecker ComplexOrder
open Matrix

noncomputable section

namespace FreeEntropy.Channels

set_option autoImplicit false

variable {ι α β : Type*} [Fintype ι] [Fintype α] [Fintype β]

/-- Schrödinger-picture Kraus formula. -/
def krausMap (K : ι → Matrix β α ℂ) (X : Matrix α α ℂ) : Matrix β β ℂ :=
  ∑ i, K i * X * (K i)ᴴ

theorem krausMap_positive (K : ι → Matrix β α ℂ)
    {X : Matrix α α ℂ} (hX : X.PosSemidef) : (krausMap K X).PosSemidef := by
  apply Matrix.posSemidef_sum
  intro i _
  exact hX.mul_mul_conjTranspose_same (K i)

omit [Fintype β] in
theorem krausMap_add (K : ι → Matrix β α ℂ) (X Y : Matrix α α ℂ) :
    krausMap K (X + Y) = krausMap K X + krausMap K Y := by
  simp [krausMap, Matrix.mul_add, Matrix.add_mul, Finset.sum_add_distrib]

omit [Fintype β] in
theorem krausMap_smul (K : ι → Matrix β α ℂ) (c : ℂ) (X : Matrix α α ℂ) :
    krausMap K (c • X) = c • krausMap K X := by
  simp [krausMap, Matrix.mul_smul, Matrix.smul_mul, Finset.smul_sum]

/-- The dual identity ∑ K* K = I implies exact trace preservation. -/
theorem krausMap_trace [DecidableEq α] (K : ι → Matrix β α ℂ)
    (hK : ∑ i, (K i)ᴴ * K i = 1) (X : Matrix α α ℂ) :
    Matrix.trace (krausMap K X) = Matrix.trace X := by
  calc
    Matrix.trace (krausMap K X) = ∑ i, Matrix.trace ((K i)ᴴ * K i * X) := by
      simp only [krausMap, Matrix.trace_sum]
      apply Finset.sum_congr rfl
      intro i _
      rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc]
    _ = Matrix.trace ((∑ i, (K i)ᴴ * K i) * X) := by
      rw [Matrix.sum_mul, Matrix.trace_sum]
    _ = Matrix.trace X := by rw [hK, Matrix.one_mul]

/-- Applying a map to each ancilla matrix block: the actual matrix amplification. -/
def amplify {κ : Type*} (Φ : Matrix α α ℂ → Matrix β β ℂ)
    (X : Matrix (κ × α) (κ × α) ℂ) : Matrix (κ × β) (κ × β) ℂ :=
  fun a b => Φ (fun i j => X (a.1, i) (b.1, j)) a.2 b.2

omit [Fintype β] in
theorem amplify_krausMap {κ : Type*} [Fintype κ] [DecidableEq κ]
    (K : ι → Matrix β α ℂ) (X : Matrix (κ × α) (κ × α) ℂ) :
    amplify (krausMap K) X =
      krausMap (fun i => (1 : Matrix κ κ ℂ) ⊗ₖ K i) X := by
  ext ⟨a, i⟩ ⟨b, j⟩
  simp [amplify, krausMap, Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Fintype.sum_prod_type, Matrix.one_apply, apply_ite]

/-- Every finite amplification preserves positive semidefinite matrices. -/
theorem krausMap_completely_positive {κ : Type*} [Fintype κ] [DecidableEq κ]
    (K : ι → Matrix β α ℂ) {X : Matrix (κ × α) (κ × α) ℂ}
    (hX : X.PosSemidef) : (amplify (krausMap K) X).PosSemidef := by
  rw [amplify_krausMap]
  exact krausMap_positive _ hX

/-- One transparent finite-dimensional channel structure. -/
structure MatrixChannel (α β : Type*) [Fintype α] [Fintype β] where
  toFun : Matrix α α ℂ → Matrix β β ℂ
  map_add : ∀ X Y, toFun (X + Y) = toFun X + toFun Y
  map_smul : ∀ (c : ℂ) X, toFun (c • X) = c • toFun X
  trace_preserving : ∀ X, Matrix.trace (toFun X) = Matrix.trace X
  positive : ∀ X, X.PosSemidef → (toFun X).PosSemidef
  completely_positive : ∀ (k : ℕ) (X : Matrix (Fin k × α) (Fin k × α) ℂ),
    X.PosSemidef → (amplify toFun X).PosSemidef

/-- A channel constructed from normalized Kraus matrices, with all laws proved. -/
def ofKraus [DecidableEq α] (K : ι → Matrix β α ℂ)
    (hK : ∑ i, (K i)ᴴ * K i = 1) : MatrixChannel α β where
  toFun := krausMap K
  map_add := krausMap_add K
  map_smul := krausMap_smul K
  trace_preserving := krausMap_trace K hK
  positive := fun _ hX => krausMap_positive K hX
  completely_positive := fun _ _ hX => krausMap_completely_positive K hX

/-- A channel has an ordinary complex-linear map, usable by the orbit proofs. -/
def MatrixChannel.toLinearMap (Φ : MatrixChannel α β) :
    Matrix α α ℂ →ₗ[ℂ] Matrix β β ℂ where
  toFun := Φ.toFun
  map_add' := Φ.map_add
  map_smul' := Φ.map_smul

/-- Restricting scalars gives the real-linear map used in trace inequalities. -/
def MatrixChannel.toRealLinearMap (Φ : MatrixChannel α β) :
    Matrix α α ℂ →ₗ[ℝ] Matrix β β ℂ where
  toFun := Φ.toFun
  map_add' := Φ.map_add
  map_smul' := by
    intro r X
    simpa only [Complex.coe_smul] using Φ.map_smul (r : ℂ) X

/-- Composition of concrete channels is again a concrete channel. -/
def MatrixChannel.comp {γ : Type*} [Fintype γ]
    (Ψ : MatrixChannel β γ) (Φ : MatrixChannel α β) : MatrixChannel α γ where
  toFun := fun X => Ψ.toFun (Φ.toFun X)
  map_add := by intro X Y; rw [Φ.map_add, Ψ.map_add]
  map_smul := by intro c X; rw [Φ.map_smul, Ψ.map_smul]
  trace_preserving := by intro X; rw [Ψ.trace_preserving, Φ.trace_preserving]
  positive := fun X hX => Ψ.positive _ (Φ.positive X hX)
  completely_positive := by
    intro k X hX
    exact Ψ.completely_positive k _ (Φ.completely_positive k X hX)

/-- The Kraus adjoint with respect to the trace pairing. -/
def krausAdjoint (K : ι → Matrix β α ℂ) (Y : Matrix β β ℂ) : Matrix α α ℂ :=
  ∑ i, (K i)ᴴ * Y * K i

/-- The adjoint formula is proved for arbitrary matrices, not only states. -/
theorem trace_krausMap_pairing (K : ι → Matrix β α ℂ)
    (X : Matrix α α ℂ) (Y : Matrix β β ℂ) :
    Matrix.trace (krausMap K X * Y) = Matrix.trace (X * krausAdjoint K Y) := by
  simp only [krausMap, krausAdjoint, Matrix.sum_mul, Matrix.mul_sum, Matrix.trace_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [Matrix.mul_assoc, Matrix.mul_assoc, Matrix.trace_mul_comm (K i)]
  simp only [Matrix.mul_assoc]

/-- Omitting all but one Kraus branch leaves a positive remainder. This is
the actual matrix positivity step used when retaining the highest weight. -/
theorem krausMap_sub_branch_positive (K : ι → Matrix β α ℂ) (k : ι)
    {X : Matrix α α ℂ} (hX : X.PosSemidef) :
    (krausMap K X - K k * X * (K k).conjTranspose).PosSemidef := by
  classical
  have hsum := Finset.sum_erase_add Finset.univ
    (fun i => K i * X * (K i).conjTranspose) (Finset.mem_univ k)
  unfold krausMap
  rw [← hsum, add_sub_cancel_right]
  apply Matrix.posSemidef_sum
  intro i _
  exact hX.mul_mul_conjTranspose_same (K i)

/-- A retained Kraus branch has at most the input trace. -/
theorem kraus_branch_trace_le [DecidableEq α]
    (K : ι → Matrix β α ℂ) (hK : ∑ i, (K i)ᴴ * K i = 1) (k : ι)
    {X : Matrix α α ℂ} (hX : X.PosSemidef) :
    (Matrix.trace (K k * X * (K k).conjTranspose)).re ≤ (Matrix.trace X).re := by
  have h := (krausMap_sub_branch_positive K k hX).trace_nonneg.1
  rw [Matrix.trace_sub, krausMap_trace K hK, Complex.sub_re] at h
  exact sub_nonneg.mp h

end FreeEntropy.Channels
