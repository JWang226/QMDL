/-
Copyright (c) 2026 Free Entropy formalization contributors.
See LICENSE and NOTICE in the repository root for license and attribution.
-/

import FreeEntropy.TraceCloning

/-! Explicit zero-difference realization. The positive-difference Casimir
adapter is unnecessary when the input and output representation coincide. -/
noncomputable section
open scoped BigOperators MatrixOrder ComplexOrder
namespace FreeEntropy.TraceCloning
set_option backward.isDefEq.respectTransparency false
open Matrix Channels CloningMatrices TraceDistance OrbitMemory

variable {H ι : Type*} [Fintype H] [DecidableEq H]

/-- Identity as an actual CPTP map, proved using its one Kraus operator. -/
def identityChannel : MatrixChannel H H :=
  ofKraus (fun _ : Unit => (1 : Matrix H H ℂ)) (by simp)

@[simp] theorem identityChannel_apply (X : Matrix H H ℂ) :
    (identityChannel (H := H)).toFun X = X := by
  simp [identityChannel, ofKraus, krausMap]

/-- Coincident state blocks give a zero-deficit realization with identity
channels. This supplies the endpoint excluded by the positive-D Casimir adapter. -/
def identityRealization (s : Finset ι) (m : ι → ℕ) (p : ι → ℝ)
    (P : ι → Matrix H H ℂ) (hP : ∀ i ∈ s, (P i).PosSemidef)
    (htr : ∀ i ∈ s, tr (P i) = (m i : ℝ))
    (hnorm : (mixture s p P).trace = 1) :
    TraceBlockRealization s m m p p (fun _ => 0) 1 H H where
  Pμ := P
  Pν := P
  Cμ := P
  Cν := P
  forward := identityChannel
  reverse := identityChannel
  positive_μ := hP
  positive_ν := hP
  compressed_positive_ν := hP
  trace_μ := htr
  trace_ν := htr
  normalized_μ := hnorm
  normalized_ν := hnorm
  deficit_positive_μ i _ := by simpa only [sub_self] using (Matrix.PosSemidef.zero (n := H) (R := ℂ))
  deficit_positive_ν i _ := by simpa only [sub_self] using (Matrix.PosSemidef.zero (n := H) (R := ℂ))
  deficit_trace_μ i _ := by simp [tr]
  deficit_trace_ν i _ := by simp [tr]
  branch_forward := by
    rw [one_smul, identityChannel_apply]
  branch_reverse := by simp

/-- Both actual channel errors vanish in the explicit identity realization. -/
theorem identityRealization_errors (s : Finset ι) (m : ι → ℕ) (p : ι → ℝ)
    (P : ι → Matrix H H ℂ) (hP : ∀ i ∈ s, (P i).PosSemidef)
    (htr : ∀ i ∈ s, tr (P i) = (m i : ℝ)) (hnorm : (mixture s p P).trace = 1) :
    traceDistance ((identityRealization s m p P hP htr hnorm).forward.toFun (mixture s p P))
      (mixture s p P) = 0 ∧
    traceDistance ((identityRealization s m p P hP htr hnorm).reverse.toFun (mixture s p P))
      (mixture s p P) = 0 := by
  simp [identityRealization, traceDistance, traceNorm, tr]

end FreeEntropy.TraceCloning
