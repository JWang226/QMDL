/-
Copyright (c) 2026 Free Entropy formalization contributors.
See LICENSE and NOTICE in the repository root for license and attribution.
-/

import FreeEntropy.SchurProtocol
import FreeEntropy.SpectralProjector
import Mathlib.Data.Matrix.Basis

/-!
# Explicit CPTP fallback channels on atypical sectors

The replacement channel has Kraus operators `|target⟩⟨a|`, indexed by the
input basis. Its output is exactly the input trace times the chosen pure
state. Channels supplied only on the typical subtype are extended to all
sectors by this concrete fallback, and the finite compression bound follows
without any assumptions about atypical channel existence or accuracy.
-/

noncomputable section
open scoped BigOperators Matrix ComplexOrder MatrixOrder
open Matrix

namespace FreeEntropy.AtypicalChannels
open Channels SpectralProjector TraceDistance

set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false

variable {H T : Type*} [Fintype H] [Fintype T] [DecidableEq H] [DecidableEq T]

/-- The standard matrix unit `|target⟩⟨a|`. -/
def replacementKraus (target : T) (a : H) : Matrix T H ℂ := Matrix.single target a 1

theorem replacementKraus_normalization (target : T) :
    (∑ a : H, (replacementKraus target a)ᴴ * replacementKraus target a) = 1 := by
  simp [replacementKraus, Matrix.sum_single_one]

theorem single_eq_coordinateProjection (target : T) :
    Matrix.single target target (1 : ℂ) = coordinateProjection target := by
  ext i j
  by_cases hi : target = i <;> by_cases hj : target = j <;>
    simp [Matrix.single, coordinateProjection, Matrix.diagonal_apply, hi, hj, eq_comm]

/-- The pure-state replacement operation is CPTP on arbitrary finite inputs. -/
def replacementChannel (target : T) : MatrixChannel H T :=
  ofKraus (replacementKraus target) (replacementKraus_normalization target)

/-- The formula is proved for every matrix, including unnormalized inputs. -/
theorem replacementChannel_apply (target : T) (X : Matrix H H ℂ) :
    (replacementChannel target).toFun X = X.trace • coordinateProjection target := by
  simp only [replacementChannel, ofKraus, krausMap, replacementKraus,
    Matrix.conjTranspose_single, star_one, Matrix.single_mul_mul_single, one_mul, mul_one]
  rw [← single_eq_coordinateProjection, Matrix.smul_single]
  ext i j
  by_cases hi : target = i <;> by_cases hj : target = j <;>
    simp [Matrix.single, Matrix.trace, Matrix.diag, Matrix.sum_apply, hi, hj]

/-- Every trace-one input is sent to the chosen basis pure state. -/
theorem replacementChannel_state (target : T) (X : Matrix H H ℂ) (hX : X.trace = 1) :
    (replacementChannel target).toFun X = coordinateProjection target := by
  rw [replacementChannel_apply, hX, one_smul]

/-- Nonempty output spaces supply a fixed pure-state fallback automatically. -/
def defaultReplacement [Nonempty T] : MatrixChannel H T :=
  replacementChannel (Classical.choice (inferInstance : Nonempty T))

theorem defaultReplacement_state [Nonempty T] (X : Matrix H H ℂ) (hX : X.trace = 1) :
    (defaultReplacement (H := H) (T := T)).toFun X =
      coordinateProjection (Classical.choice (inferInstance : Nonempty T)) :=
  replacementChannel_state _ X hX

section TypicalExtension

variable {ι M : Type*} [Fintype ι] [DecidableEq ι] [Fintype M] [DecidableEq M]
variable {B : ι → Type*} [∀ i, Fintype (B i)] [∀ i, DecidableEq (B i)]

/-- Extend typical forward channels by a fixed pure-state replacement on
every atypical sector. Each branch is an actual CPTP channel. -/
def extendForward [Nonempty M] (typical : Finset ι)
    (F : ∀ i : {i // i ∈ typical}, MatrixChannel (B i.1) M) (i : ι) :
    MatrixChannel (B i) M :=
  if hi : i ∈ typical then F ⟨i, hi⟩ else defaultReplacement

/-- Extend typical reverse channels by an automatically chosen pure state
in each atypical output sector. -/
def extendReverse [∀ i, Nonempty (B i)] (typical : Finset ι)
    (G : ∀ i : {i // i ∈ typical}, MatrixChannel M (B i.1)) (i : ι) :
    MatrixChannel M (B i) :=
  if hi : i ∈ typical then G ⟨i, hi⟩ else defaultReplacement

theorem extendForward_of_mem [Nonempty M] (typical : Finset ι)
    (F : ∀ i : {i // i ∈ typical}, MatrixChannel (B i.1) M) (i : ι) (hi : i ∈ typical) :
    extendForward typical F i = F ⟨i, hi⟩ := by simp [extendForward, hi]

theorem extendReverse_of_mem [∀ i, Nonempty (B i)] (typical : Finset ι)
    (G : ∀ i : {i // i ∈ typical}, MatrixChannel M (B i.1)) (i : ι) (hi : i ∈ typical) :
    extendReverse typical G i = G ⟨i, hi⟩ := by simp [extendReverse, hi]

theorem extendForward_of_not_mem [Nonempty M] (typical : Finset ι)
    (F : ∀ i : {i // i ∈ typical}, MatrixChannel (B i.1) M) (i : ι) (hi : i ∉ typical) :
    extendForward typical F i = defaultReplacement := by simp [extendForward, hi]

theorem extendReverse_of_not_mem [∀ i, Nonempty (B i)] (typical : Finset ι)
    (G : ∀ i : {i // i ∈ typical}, MatrixChannel M (B i.1)) (i : ι) (hi : i ∉ typical) :
    extendReverse typical G i = defaultReplacement := by simp [extendReverse, hi]

variable {A : ι → Type*} [∀ i, Fintype (A i)] [∀ i, DecidableEq (A i)]
  [∀ i, Nonempty (A i)] [∀ i, Nonempty (B i)] [Nonempty M]

/-- Complete finite Schur-sector compression with channels required only
on the typical subtype. Atypical CPTP maps are constructed by replacement,
and all multiplicity registers are discarded and restored explicitly. -/
theorem typical_subtype_roundtrip_error (typical : Finset ι)
    (F : ∀ i : {i // i ∈ typical}, MatrixChannel (B i.1) M)
    (G : ∀ i : {i // i ∈ typical}, MatrixChannel M (B i.1))
    (q : ι → ℝ) (hq0 : ∀ i, 0 ≤ q i) (hq1 : ∑ i, q i = 1)
    (σ : ∀ i, Matrix (B i) (B i) ℂ) (hσ : ∀ i, (σ i).PosSemidef)
    (htσ : ∀ i, (σ i).trace = 1) (τ : Matrix M M ℂ)
    (hτ : τ.PosSemidef) (htτ : τ.trace = 1) (ε : ℝ) (hε : 0 ≤ ε)
    (hf : ∀ i : {i // i ∈ typical}, traceDistance ((F i).toFun (σ i.1)) τ ≤ ε)
    (hr : ∀ i : {i // i ∈ typical}, traceDistance ((G i).toFun τ) (σ i.1) ≤ ε) :
    traceDistance ((SchurProtocol.decoder (A := A) (extendReverse typical G) q hq0 hq1).toFun
      ((SchurProtocol.encoder (A := A) (extendForward typical F)).toFun
        (SchurProtocol.sourceState (A := A) q σ))) (SchurProtocol.sourceState (A := A) q σ) ≤
      2 * ε + 2 * Protocol.outsideMass Finset.univ typical q := by
  apply SchurProtocol.typical_roundtrip_error (extendForward typical F) (extendReverse typical G)
    q hq0 hq1 σ hσ htσ τ hτ htτ typical ε hε
  · intro i hi
    rw [extendForward_of_mem typical F i hi]
    exact hf ⟨i, hi⟩
  · intro i hi
    rw [extendReverse_of_mem typical G i hi]
    exact hr ⟨i, hi⟩

end TypicalExtension

end FreeEntropy.AtypicalChannels
