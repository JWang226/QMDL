/-
Copyright (c) 2026 Free Entropy formalization contributors.
See LICENSE and NOTICE in the repository root for license and attribution.
-/

import FreeEntropy.OrbitTraceDistance
import FreeEntropy.SpectralProjector

/-!
# Compact irreducible orbit bounds from actual matrix eigenvalues

The peak projection is constructed from the matrix spectral theorem. These
corollaries take a positive matrix and an isolated largest eigenvalue; there
is no supplied projector, twirling identity, spectral operator inequality,
trace-distance testing estimate, or integrability assumption.
-/

open scoped MatrixOrder ComplexOrder Matrix.Norms.Elementwise
open Matrix MeasureTheory MeasureTheory.Measure
open FreeEntropy.OrbitMemory FreeEntropy.TraceDistance FreeEntropy.Twirling
open FreeEntropy.OrbitTraceDistance FreeEntropy.SpectralProjector

namespace FreeEntropy.OrbitEigenvalues

set_option backward.isDefEq.respectTransparency false

variable {H M G : Type*} [Fintype H] [DecidableEq H]
  [Fintype M] [DecidableEq M]
  [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [MeasurableSpace G] [BorelSpace G]

/-- The memory lower bound for an irreducible orbit, stated entirely in
terms of a positive matrix and bounds on its actual eigenvalues. -/
theorem irreducible_orbit_memory_bound_of_eigenvalues [Nonempty H]
    (μ : Measure G) [IsMulLeftInvariant μ] [IsProbabilityMeasure μ]
    (U : G →* Matrix H H ℂ) (hU : Continuous U)
    (hunitary : ∀ g, (U g)ᴴ * U g = 1)
    [Representation.IsIrreducible (matrixRepresentation U)]
    (E : Matrix H H ℂ →ₗ[ℝ] Matrix M M ℂ)
    (D : Matrix M M ℂ →ₗ[ℝ] Matrix H H ℂ)
    (hE : ∀ A, A.PosSemidef → (E A).PosSemidef)
    (hD : ∀ A, A.PosSemidef → (D A).PosSemidef)
    (hEt : ∀ A, (E A).trace = A.trace)
    (hDt : ∀ A, (D A).trace = A.trace)
    (τ : Matrix H H ℂ) (hτ : τ.PosSemidef) (k : H) (p₁ : ℝ)
    (hother : ∀ i, i ≠ k → hτ.isHermitian.eigenvalues i ≤ p₁)
    (hgap : 0 < hτ.isHermitian.eigenvalues k - p₁) :
    (Fintype.card H : ℝ) * (1 -
      (∫ g, traceDistance (D (E (U g * τ * (U g)ᴴ))) (U g * τ * (U g)ᴴ) ∂μ) /
        (hτ.isHermitian.eigenvalues k - p₁)) ≤ (Fintype.card M : ℝ) := by
  exact irreducible_orbit_memory_bound μ U hU hunitary E D hE hD hEt hDt
    (eigenProjection hτ.isHermitian k) τ
    (eigenProjection_pos hτ.isHermitian k) (eigenProjection_trace hτ.isHermitian k) hτ hgap
    (eigenProjection_peak hτ.isHermitian k)
    (spectral_upper_bound hτ.isHermitian k rfl hother)

/-- Fixed-spectrum form of the eigenvalue-only orbit bound. -/
theorem irreducible_orbit_memory_bound_gammaX_of_eigenvalues [Nonempty H]
    {d r : ℕ} (s : FixedSpectrum d r)
    (μ : Measure G) [IsMulLeftInvariant μ] [IsProbabilityMeasure μ]
    (U : G →* Matrix H H ℂ) (hU : Continuous U)
    (hunitary : ∀ g, (U g)ᴴ * U g = 1)
    [Representation.IsIrreducible (matrixRepresentation U)]
    (E : Matrix H H ℂ →ₗ[ℝ] Matrix M M ℂ)
    (D : Matrix M M ℂ →ₗ[ℝ] Matrix H H ℂ)
    (hE : ∀ A, A.PosSemidef → (E A).PosSemidef)
    (hD : ∀ A, A.PosSemidef → (D A).PosSemidef)
    (hEt : ∀ A, (E A).trace = A.trace)
    (hDt : ∀ A, (D A).trace = A.trace)
    (τ : Matrix H H ℂ) (hτ : τ.PosSemidef) (k : H) (p₁ : ℝ)
    (hother : ∀ i, i ≠ k → hτ.isHermitian.eigenvalues i ≤ p₁)
    (htop : s.spectralProduct ≤ hτ.isHermitian.eigenvalues k)
    (hnext : p₁ ≤ s.qx * hτ.isHermitian.eigenvalues k) :
    (Fintype.card H : ℝ) * (1 -
      (∫ g, traceDistance (D (E (U g * τ * (U g)ᴴ))) (U g * τ * (U g)ᴴ) ∂μ) /
        s.gammaX) ≤ (Fintype.card M : ℝ) := by
  exact irreducible_orbit_memory_bound_gammaX s μ U hU hunitary E D hE hD hEt hDt
    (eigenProjection hτ.isHermitian k) τ
    (eigenProjection_pos hτ.isHermitian k) (eigenProjection_trace hτ.isHermitian k) hτ htop hnext
    (eigenProjection_peak hτ.isHermitian k)
    (spectral_upper_bound hτ.isHermitian k rfl hother)

/-- Build the concrete orbit-code interface used in the asymptotic converse
from actual eigenvalue inequalities and CPTP maps. The spectral projector and
all its trace/operator properties are constructed, not supplied. -/
noncomputable def orbitCodeOfEigenvalues
    {d r target memory : ℕ} (s : FixedSpectrum d r)
    (U : G →* Matrix (Fin target) (Fin target) ℂ) (hU : Continuous U)
    (hunitary : ∀ g, (U g)ᴴ * U g = 1)
    [Representation.IsIrreducible (matrixRepresentation U)]
    (E : Channels.MatrixChannel (Fin target) (Fin memory))
    (D : Channels.MatrixChannel (Fin memory) (Fin target))
    (τ : Matrix (Fin target) (Fin target) ℂ) (hτ : τ.PosSemidef) (hτt : τ.trace = 1)
    (k : Fin target) (p₁ : ℝ)
    (hother : ∀ i, i ≠ k → hτ.isHermitian.eigenvalues i ≤ p₁)
    (htop : s.spectralProduct ≤ hτ.isHermitian.eigenvalues k)
    (hnext : p₁ ≤ s.qx * hτ.isHermitian.eigenvalues k) :
    OrbitCode s G target memory where
  U := U
  continuous_U := hU
  unitary := hunitary
  irreducible := inferInstance
  encoder := E
  decoder := D
  state := τ
  state_positive := hτ
  state_trace_one := hτt
  peak := eigenProjection hτ.isHermitian k
  peak_positive := eigenProjection_pos hτ.isHermitian k
  peak_trace_one := eigenProjection_trace hτ.isHermitian k
  top := hτ.isHermitian.eigenvalues k
  second := p₁
  peak_overlap := eigenProjection_peak hτ.isHermitian k
  spectral_upper := spectral_upper_bound hτ.isHermitian k rfl hother
  top_lower := htop
  next_upper := hnext

end FreeEntropy.OrbitEigenvalues
