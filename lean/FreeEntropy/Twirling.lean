/-
Copyright (c) 2026 Free Entropy formalization contributors.
See LICENSE and NOTICE in the repository root for license and attribution.
-/

import FreeEntropy.OrbitMemory
import Mathlib.RepresentationTheory.Irreducible
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Function.LocallyIntegrable

/-!
# Haar twirling for an actual irreducible matrix representation

The representation acts by matrices and conjugates using its group inverse.
For a unitary representation this is precisely conjugate transpose. Schur's
lemma is taken from Mathlib's `Representation.IsIrreducible` API, not assumed
as a scalar-commutant or twirling hypothesis.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

open MeasureTheory MeasureTheory.Measure Matrix
open scoped Matrix.Norms.Elementwise

namespace FreeEntropy.Twirling

variable {G H : Type*} [Group G] [Fintype H] [DecidableEq H]

/-- A matrix homomorphism viewed as a representation on coordinate vectors. -/
def matrixRepresentation (U : G →* Matrix H H ℂ) : Representation ℂ G (H → ℂ) :=
  (Matrix.toLinAlgEquiv' : Matrix H H ℂ ≃ₐ[ℂ] Module.End ℂ (H → ℂ)).toMonoidHom.comp U

/-- Schur's lemma in matrix form, proved from genuine irreducibility. -/
theorem commutant_is_scalar (U : G →* Matrix H H ℂ)
    [Representation.IsIrreducible (matrixRepresentation U)]
    (A : Matrix H H ℂ) (hA : ∀ g, A * U g = U g * A) :
    ∃ c : ℂ, A = c • (1 : Matrix H H ℂ) := by
  let f : Representation.IntertwiningMap (matrixRepresentation U) (matrixRepresentation U) :=
    { toLinearMap := Matrix.toLinAlgEquiv' A
      isIntertwining' g := by
        change Matrix.toLinAlgEquiv' A * Matrix.toLinAlgEquiv' (U g) =
          Matrix.toLinAlgEquiv' (U g) * Matrix.toLinAlgEquiv' A
        rw [← map_mul, ← map_mul, hA g] }
  obtain ⟨c, hc⟩ :=
    (Representation.IsIrreducible.algebraMap_intertwiningMap_bijective_of_isAlgClosed
      (ρ := matrixRepresentation U)).2 f
  refine ⟨c, ?_⟩
  apply (Matrix.toLinAlgEquiv' : Matrix H H ℂ ≃ₐ[ℂ] Module.End ℂ (H → ℂ)).injective
  have heq := congrArg (fun k : Representation.IntertwiningMap
    (matrixRepresentation U) (matrixRepresentation U) => k.toLinearMap) hc
  simpa [Representation.IntertwiningMap.algebraMap_apply, f, map_smul] using heq.symm

/-- Conjugation by the representation, written without requiring a separate
choice of matrix inverse. -/
def conjugate (U : G →* Matrix H H ℂ) (g : G) (A : Matrix H H ℂ) : Matrix H H ℂ :=
  U g * A * U g⁻¹

theorem conjugate_mul (U : G →* Matrix H H ℂ) (g h : G) (A : Matrix H H ℂ) :
    conjugate U g (conjugate U h A) = conjugate U (g * h) A := by
  simp [conjugate, map_mul, _root_.mul_inv_rev, Matrix.mul_assoc]

theorem trace_conjugate (U : G →* Matrix H H ℂ) (g : G) (A : Matrix H H ℂ) :
    (conjugate U g A).trace = A.trace := by
  unfold conjugate
  rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc, ← map_mul, inv_mul_cancel, map_one,
    Matrix.one_mul]

/-- For a unitary matrix representation its group inverse is the conjugate
transpose used in the article. -/
theorem inverse_eq_conjTranspose (U : G →* Matrix H H ℂ)
    (hunitary : ∀ g, (U g)ᴴ * U g = 1) (g : G) : U g⁻¹ = (U g)ᴴ := by
  have hi : U g * U g⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel, map_one]
  calc
    U g⁻¹ = 1 * U g⁻¹ := (Matrix.one_mul _).symm
    _ = ((U g)ᴴ * U g) * U g⁻¹ := by rw [hunitary g]
    _ = (U g)ᴴ := by rw [Matrix.mul_assoc, hi, Matrix.mul_one]

theorem conjugate_eq_unitary_conjugate (U : G →* Matrix H H ℂ)
    (hunitary : ∀ g, (U g)ᴴ * U g = 1) (g : G) (P : Matrix H H ℂ) :
    conjugate U g P = U g * P * (U g)ᴴ := by
  rw [conjugate, inverse_eq_conjTranspose U hunitary]

def conjugateCLM (U : G →* Matrix H H ℂ) (g : G) :
    Matrix H H ℂ →L[ℂ] Matrix H H ℂ :=
  LinearMap.toContinuousLinearMap
    ((LinearMap.mulRight ℂ (U g⁻¹)).comp (LinearMap.mulLeft ℂ (U g)))

@[simp] theorem conjugateCLM_apply (U : G →* Matrix H H ℂ) (g : G)
    (A : Matrix H H ℂ) : conjugateCLM U g A = conjugate U g A := rfl

def traceCLM : Matrix H H ℂ →L[ℂ] ℂ :=
  LinearMap.toContinuousLinearMap (Matrix.traceLinearMap H ℂ ℂ)

omit [DecidableEq H] in
@[simp] theorem traceCLM_apply (A : Matrix H H ℂ) : traceCLM A = A.trace := rfl

section Measure

variable [MeasurableSpace G] [MeasurableMul G]

/-- Left-Haar invariance makes the integral invariant under conjugation. -/
theorem integral_conjugate_invariant (μ : Measure G) [IsMulLeftInvariant μ]
    (U : G →* Matrix H H ℂ) (P : Matrix H H ℂ)
    (hi : Integrable (fun g => conjugate U g P) μ) (h : G) :
    conjugate U h (∫ g, conjugate U g P ∂μ) = ∫ g, conjugate U g P ∂μ := by
  calc
    _ = ∫ g, conjugate U h (conjugate U g P) ∂μ := by
      simpa only [conjugateCLM_apply] using ((conjugateCLM U h).integral_comp_comm hi).symm
    _ = ∫ g, conjugate U (h * g) P ∂μ := by simp only [conjugate_mul]
    _ = _ := integral_mul_left_eq_self (fun g => conjugate U g P) h

/-- The invariant average commutes with every representation matrix. -/
theorem integral_conjugate_commutes (μ : Measure G) [IsMulLeftInvariant μ]
    (U : G →* Matrix H H ℂ) (P : Matrix H H ℂ)
    (hi : Integrable (fun g => conjugate U g P) μ) (h : G) :
    (∫ g, conjugate U g P ∂μ) * U h = U h * (∫ g, conjugate U g P ∂μ) := by
  have hc := congrArg (fun A => A * U h) (integral_conjugate_invariant μ U P hi h)
  simpa only [conjugate, Matrix.mul_assoc, ← map_mul, inv_mul_cancel, map_one,
    Matrix.mul_one] using hc.symm

/-- Exact normalized Haar twirling. Integrability is discharged from
continuity and compactness in the theorem below. -/
theorem integral_conjugate_eq_scalar [Nonempty H]
    (μ : Measure G) [IsMulLeftInvariant μ] [IsProbabilityMeasure μ]
    (U : G →* Matrix H H ℂ)
    [Representation.IsIrreducible (matrixRepresentation U)]
    (P : Matrix H H ℂ) (hi : Integrable (fun g => conjugate U g P) μ) :
    (∫ g, conjugate U g P ∂μ) =
      (P.trace / (Fintype.card H : ℂ)) • (1 : Matrix H H ℂ) := by
  obtain ⟨c, hc⟩ := commutant_is_scalar U (∫ g, conjugate U g P ∂μ)
    (integral_conjugate_commutes μ U P hi)
  have ht : (∫ g, conjugate U g P ∂μ).trace = P.trace := by
    calc
      _ = ∫ g, (conjugate U g P).trace ∂μ := by
        simpa only [traceCLM_apply] using (traceCLM.integral_comp_comm hi).symm
      _ = ∫ _g : G, P.trace ∂μ := by simp only [trace_conjugate]
      _ = P.trace := by simp
  have hdim : (Fintype.card H : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hct : c * (Fintype.card H : ℂ) = P.trace := by
    simpa [hc, Matrix.trace_smul, Matrix.trace_one, smul_eq_mul] using ht
  have hcval : c = P.trace / (Fintype.card H : ℂ) := (eq_div_iff hdim).mpr hct
  rw [hc, hcval]

end Measure

section Compact

variable [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [MeasurableSpace G] [BorelSpace G]

theorem conjugate_integrable (μ : Measure G) [IsFiniteMeasure μ]
    (U : G →* Matrix H H ℂ) (hU : Continuous U) (P : Matrix H H ℂ) :
    Integrable (fun g => conjugate U g P) μ := by
  have hc : Continuous (fun g => conjugate U g P) :=
    (hU.mul continuous_const).mul (hU.comp continuous_inv)
  exact hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

/-- A continuous irreducible representation of a compact group has the
normalized Haar twirl asserted in the manuscript. No twirling or commutant
hypothesis is present. -/
theorem compact_irreducible_twirl [Nonempty H]
    (μ : Measure G) [IsMulLeftInvariant μ] [IsProbabilityMeasure μ]
    (U : G →* Matrix H H ℂ) (hU : Continuous U)
    [Representation.IsIrreducible (matrixRepresentation U)]
    (P : Matrix H H ℂ) :
    (∫ g, conjugate U g P ∂μ) =
      (P.trace / (Fintype.card H : ℂ)) • (1 : Matrix H H ℂ) :=
  integral_conjugate_eq_scalar μ U P (conjugate_integrable μ U hU P)

/-- The usual dagger notation for Haar twirling of a continuous irreducible
unitary representation of a compact group. -/
theorem compact_irreducible_unitary_twirl [Nonempty H]
    (μ : Measure G) [IsMulLeftInvariant μ] [IsProbabilityMeasure μ]
    (U : G →* Matrix H H ℂ) (hU : Continuous U)
    (hunitary : ∀ g, (U g)ᴴ * U g = 1)
    [Representation.IsIrreducible (matrixRepresentation U)]
    (P : Matrix H H ℂ) :
    (∫ g, U g * P * (U g)ᴴ ∂μ) =
      (P.trace / (Fintype.card H : ℂ)) • (1 : Matrix H H ℂ) := by
  simpa only [conjugate_eq_unitary_conjugate U hunitary] using
    compact_irreducible_twirl μ U hU P

/-- The exact real-scalar trace-one identity needed by the orbit memory
bound. Rank one and positivity are unnecessary for this averaging identity. -/
theorem compact_trace_one_unitary_twirl [Nonempty H]
    (μ : Measure G) [IsMulLeftInvariant μ] [IsProbabilityMeasure μ]
    (U : G →* Matrix H H ℂ) (hU : Continuous U)
    (hunitary : ∀ g, (U g)ᴴ * U g = 1)
    [Representation.IsIrreducible (matrixRepresentation U)]
    (P : Matrix H H ℂ) (htrace : P.trace = 1) :
    (∫ g, U g * P * (U g)ᴴ ∂μ) =
      (Fintype.card H : ℝ)⁻¹ • (1 : Matrix H H ℂ) := by
  rw [compact_irreducible_unitary_twirl μ U hU hunitary P, htrace, one_div]
  have hcoe : (((Fintype.card H : ℝ)⁻¹ : ℝ) : ℂ) = (Fintype.card H : ℂ)⁻¹ := by simp
  rw [← hcoe, Complex.coe_smul]

theorem unitary_orbit_integrable (μ : Measure G) [IsFiniteMeasure μ]
    (U : G →* Matrix H H ℂ) (hU : Continuous U)
    (hunitary : ∀ g, (U g)ᴴ * U g = 1) (P : Matrix H H ℂ) :
    Integrable (fun g => U g * P * (U g)ᴴ) μ := by
  simpa only [conjugate_eq_unitary_conjugate U hunitary] using
    conjugate_integrable μ U hU P

end Compact

end FreeEntropy.Twirling
