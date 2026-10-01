/-
Copyright (c) 2026 Free Entropy formalization contributors.
See LICENSE and NOTICE in the repository root for license and attribution.
-/

import FreeEntropy.TraceMetric
import FreeEntropy.Protocol
import FreeEntropy.Statements

/-!
# Concrete trace-distance bounds for compression and code transfer

The triangle, convexity and contraction arguments here concern actual
complex matrices and CPTP channels. In particular the decoder may resample
its output sector independently: no assumption that sector labels agree
across the encoding/decoding steps is made.
-/

noncomputable section
open scoped BigOperators MatrixOrder ComplexOrder Topology
open Matrix FreeEntropy.OrbitMemory FreeEntropy.TraceDistance
open FreeEntropy.Channels FreeEntropy.CloningMatrices
namespace FreeEntropy.QuantumProtocol
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false

variable {S T M ι : Type*} [Fintype S] [DecidableEq S]
  [Fintype T] [DecidableEq T] [Fintype M] [DecidableEq M]

/-- The reference-target triangle bound for two actual channels. -/
theorem roundtrip_error (A : MatrixChannel S T) (B : MatrixChannel T S)
    {ρ : Matrix S S ℂ} {τ : Matrix T T ℂ} (hρ : ρ.PosSemidef) (hτ : τ.PosSemidef) :
    traceDistance (B.toFun (A.toFun ρ)) ρ ≤
      traceDistance (A.toFun ρ) τ + traceDistance (B.toFun τ) ρ := by
  have ht := traceDistance_triangle
    (B.positive _ (A.positive _ hρ)).isHermitian (B.positive _ hτ).isHermitian hρ.isHermitian
  have hc := traceDistance_contract B.toRealLinearMap B.positive B.trace_preserving
    (A.positive _ hρ) hτ
  change traceDistance (B.toFun (A.toFun ρ)) (B.toFun τ) ≤ traceDistance (A.toFun ρ) τ at hc
  linarith

/-- Transfer an arbitrary source code to the orbit using actual CPTP maps.
All contractivity and triangle hypotheses of the old metric lemma disappear. -/
theorem transferred_code_error (A : MatrixChannel S T) (B : MatrixChannel T S)
    (E : MatrixChannel S M) (D : MatrixChannel M S)
    {ρ : Matrix S S ℂ} {τ : Matrix T T ℂ} (hρ : ρ.PosSemidef) (hτ : τ.PosSemidef) :
    traceDistance (A.toFun (D.toFun (E.toFun (B.toFun τ)))) τ ≤
      traceDistance (B.toFun τ) ρ + traceDistance (D.toFun (E.toFun ρ)) ρ +
        traceDistance (A.toFun ρ) τ := by
  have hBτ := B.positive _ hτ
  have hEDBτ := D.positive _ (E.positive _ hBτ)
  have hEDρ := D.positive _ (E.positive _ hρ)
  have hAρ := A.positive _ hρ
  have htri := traceDistance_triangle (A.positive _ hEDBτ).isHermitian
    (A.positive _ hEDρ).isHermitian hτ.isHermitian
  have htri' := traceDistance_triangle (A.positive _ hEDρ).isHermitian hAρ.isHermitian hτ.isHermitian
  have hcA := traceDistance_contract A.toRealLinearMap A.positive A.trace_preserving hEDBτ hEDρ
  have hcD := traceDistance_contract D.toRealLinearMap D.positive D.trace_preserving
    (E.positive _ hBτ) (E.positive _ hρ)
  have hcE := traceDistance_contract E.toRealLinearMap E.positive E.trace_preserving hBτ hρ
  have hcA' := traceDistance_contract A.toRealLinearMap A.positive A.trace_preserving hEDρ hρ
  change traceDistance (A.toFun (D.toFun (E.toFun (B.toFun τ))))
    (A.toFun (D.toFun (E.toFun ρ))) ≤ _ at hcA
  change traceDistance (D.toFun (E.toFun (B.toFun τ))) (D.toFun (E.toFun ρ)) ≤ _ at hcD
  change traceDistance (E.toFun (B.toFun τ)) (E.toFun ρ) ≤ _ at hcE
  change traceDistance (A.toFun (D.toFun (E.toFun ρ))) (A.toFun ρ) ≤ _ at hcA'
  linarith

/-- The exact weighted error bound, accounting for independent resampling
of the decoder's output sectors. The hypotheses identify state formulas,
not trace-distance estimates. -/
theorem mixture_roundtrip_error (s : Finset ι) (q : ι → ℝ)
    (E : MatrixChannel S M) (D : MatrixChannel M S)
    (source rebuilt : ι → Matrix S S ℂ) (encoded : ι → Matrix M M ℂ)
    (τ : Matrix M M ℂ)
    (hq : ∀ i ∈ s, 0 ≤ q i) (hsum : ∑ i ∈ s, q i = 1)
    (hsource : ∀ i ∈ s, (source i).PosSemidef)
    (hencoded : ∀ i ∈ s, (encoded i).PosSemidef)
    (hrebuilt : ∀ i ∈ s, (rebuilt i).PosSemidef) (hτ : τ.PosSemidef)
    (hencode : E.toFun (mixture s q source) = mixture s q encoded)
    (hdecode : D.toFun τ = mixture s q rebuilt) :
    traceDistance (D.toFun (E.toFun (mixture s q source))) (mixture s q source) ≤
      (∑ i ∈ s, q i * traceDistance (encoded i) τ) +
        ∑ i ∈ s, q i * traceDistance (rebuilt i) (source i) := by
  have h := roundtrip_error E D (mixture_positive s q source hq hsource) hτ
  rw [hencode, hdecode] at h
  have hf := traceDistance_mixture_le s q encoded τ hq hsum
    (fun i hi => (hencoded i hi).isHermitian) hτ.isHermitian
  have hr := traceDistance_mixtures_le s q rebuilt source hq
    (fun i hi => (hrebuilt i hi).isHermitian) (fun i hi => (hsource i hi).isHermitian)
  simpa only [hencode] using h.trans (add_le_add hf hr)

/-- Typical-sector accuracy and atypical mass imply the paper's `2ε+2tail`
bound for the actual reconstructed source matrix. -/
theorem typical_roundtrip_error [DecidableEq ι] (s typical : Finset ι) (q : ι → ℝ)
    (E : MatrixChannel S M) (D : MatrixChannel M S)
    (source rebuilt : ι → Matrix S S ℂ) (encoded : ι → Matrix M M ℂ)
    (τ : Matrix M M ℂ) (ε : ℝ)
    (hq : ∀ i ∈ s, 0 ≤ q i) (hsum : ∑ i ∈ s, q i = 1) (hε : 0 ≤ ε)
    (hsource : ∀ i ∈ s, (source i).PosSemidef)
    (hencoded : ∀ i ∈ s, (encoded i).PosSemidef)
    (hrebuilt : ∀ i ∈ s, (rebuilt i).PosSemidef) (hτ : τ.PosSemidef)
    (htsource : ∀ i ∈ s, (source i).trace = 1)
    (htencoded : ∀ i ∈ s, (encoded i).trace = 1)
    (htrebuilt : ∀ i ∈ s, (rebuilt i).trace = 1) (htτ : τ.trace = 1)
    (hencode : E.toFun (mixture s q source) = mixture s q encoded)
    (hdecode : D.toFun τ = mixture s q rebuilt)
    (hf : ∀ i ∈ s, i ∈ typical → traceDistance (encoded i) τ ≤ ε)
    (hr : ∀ i ∈ s, i ∈ typical → traceDistance (rebuilt i) (source i) ≤ ε) :
    traceDistance (D.toFun (E.toFun (mixture s q source))) (mixture s q source) ≤
      2 * ε + 2 * Protocol.outsideMass s typical q := by
  apply Protocol.roundtrip_error_le s typical q
    (fun i => traceDistance (encoded i) τ) (fun i => traceDistance (rebuilt i) (source i))
    ε _ hq hsum hε hf hr
  · intro i hi
    exact traceDistance_states_le_one (hencoded i hi) hτ (htencoded i hi) htτ
  · intro i hi
    exact traceDistance_states_le_one (hrebuilt i hi) (hsource i hi) (htrebuilt i hi) (htsource i hi)
  · exact mixture_roundtrip_error s q E D source rebuilt encoded τ hq hsum hsource hencoded hrebuilt
      hτ hencode hdecode

end FreeEntropy.QuantumProtocol
