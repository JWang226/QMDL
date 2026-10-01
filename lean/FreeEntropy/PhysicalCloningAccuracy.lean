/-
Copyright (c) 2026 Free Entropy formalization contributors.
See LICENSE and NOTICE in the repository root for license and attribution.
-/

import FreeEntropy.PhysicalCloningChannels
import FreeEntropy.CanonicalCloningOrbit
import FreeEntropy.PhysicalCanonicalConverse

/-! Uniform error estimates for the fully constructed physical comparison
channels. There are no supplied decomposition, concentration, cloning,
covariance, or local error hypotheses. -/
noncomputable section
open Matrix Filter
open scoped Topology MatrixOrder ComplexOrder
namespace FreeEntropy.SchurWeyl
open Channels TraceDistance ExteriorRepresentation TypicalRows
set_option backward.isDefEq.respectTransparency false
variable {d r : ℕ}
attribute [local instance] Classical.propDecidable

/-- Every actual typical sector has the same uniform orbit-error envelope. -/
theorem typicalCartan_orbit_error_eventually (s : FixedSpectrum d r) (hd : 2 ≤ d) :
    ∀ᶠ n in atTop, ∀ i ∈ physicalTypical s n, ∀ U : Matrix.unitaryGroup (Fin d) ℂ,
    traceDistance ((typicalCartanForward s n i).toFun
      (canonicalOrbitState s (sectorHighestOccupation i).val U))
      (canonicalOrbitState s (targetCanonicalRow s n) U) ≤
        mixedComparisonConstant s hd * Weyl.errorScale n ∧
    traceDistance ((typicalCartanReverse s n i).toFun
      (canonicalOrbitState s (targetCanonicalRow s n) U))
      (canonicalOrbitState s (sectorHighestOccupation i).val U) ≤
        mixedComparisonConstant s hd * Weyl.errorScale n := by
  filter_upwards [typicalCartan_diagonal_error_eventually s hd, eventually_ge_atTop 1] with n he hn
  intro i hi U
  have h := he i hi
  rw [typicalCartanForward_of_mem s n hn i hi, typicalCartanReverse_of_mem s n hn i hi] at h ⊢
  rw [canonicalForward_orbit_error_eq s hd, canonicalReverse_orbit_error_eq s hd]
  exact h

/-- Both total physical channels have uniform errors on the claimed scale. -/
theorem mixed_comparison_error_eventually (s : FixedSpectrum d r) (hd : 2 ≤ d) :
    ∀ᶠ n in atTop, ∀ U : Matrix.unitaryGroup (Fin d) ℂ,
    traceDistance ((mixedEncoder s n).toFun (physicalSource s n U))
      (canonicalOrbitState s (targetCanonicalRow s n) U) ≤ mixedComparisonError s hd n ∧
    traceDistance ((mixedDecoder s n).toFun (canonicalOrbitState s (targetCanonicalRow s n) U))
      (physicalSource s n U) ≤ mixedComparisonError s hd n := by
  filter_upwards [typicalCartan_orbit_error_eventually s hd, eventually_ge_atTop 2] with n he hn
  intro U
  have hc := mixedComparisonConstant_nonneg s hd
  have hscale : 0 ≤ Weyl.errorScale n := by
    unfold Weyl.errorScale
    exact div_nonneg (Real.logb_nonneg (by norm_num) (by exact_mod_cast (show 1 ≤ n by omega)))
      (Real.sqrt_nonneg _)
  have hτ := canonicalOrbitState_positive s (targetCanonicalRow s n) hd U
  have hτ1 := canonicalOrbitState_trace s (targetCanonicalRow s n) hd U
  constructor
  · exact physicalOrbit_forward_error_le s n hn (typicalCartanForward s n) U _ hτ hτ1
      _ (mul_nonneg hc hscale) (fun i hi => (he i hi U).1)
  · exact physicalOrbit_reverse_error_le s n hn (typicalCartanReverse s n) U _ hτ hτ1
      _ (mul_nonneg hc hscale) (fun i hi => (he i hi U).2)

/-- Fully derived source-to-memory approximation, uniformly in the unknown basis. -/
theorem mixedEncoder_error_eventually (s : FixedSpectrum d r) (hd : 2 ≤ d) :
    ∀ᶠ n in atTop, ∀ U : Matrix.unitaryGroup (Fin d) ℂ,
    traceDistance ((mixedEncoder s n).toFun (physicalSource s n U))
      (canonicalOrbitState s (targetCanonicalRow s n) U) ≤ mixedComparisonError s hd n :=
  (mixed_comparison_error_eventually s hd).mono (fun _ h U => (h U).1)

/-- Fully derived memory-to-source approximation, uniformly in the unknown basis. -/
theorem mixedDecoder_error_eventually (s : FixedSpectrum d r) (hd : 2 ≤ d) :
    ∀ᶠ n in atTop, ∀ U : Matrix.unitaryGroup (Fin d) ℂ,
    traceDistance ((mixedDecoder s n).toFun (canonicalOrbitState s (targetCanonicalRow s n) U))
      (physicalSource s n U) ≤ mixedComparisonError s hd n :=
  (mixed_comparison_error_eventually s hd).mono (fun _ h U => (h U).2)

end FreeEntropy.SchurWeyl
