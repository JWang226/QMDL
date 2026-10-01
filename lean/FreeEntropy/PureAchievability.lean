/-
Copyright (c) 2026 Free Entropy formalization contributors.
See LICENSE and NOTICE in the repository root for license and attribution.
-/

import FreeEntropy.PureTensorCompression
import FreeEntropy.OccupationDimension

/-!
# Unconditional rank-one achievability

The actual tensor-power source is compressed by explicit CPTP maps into
the finite occupation register. All pure vectors are recovered exactly by
the same maps. Its exact memory cardinality has the manuscript's rank-one
qmdl asymptotic. No Schur decomposition or representation premise occurs.
-/

noncomputable section
open Filter Matrix
open scoped BigOperators Topology ComplexOrder MatrixOrder

namespace FreeEntropy.PureTensorCompression
open TensorPowers Occupation TraceDistance

/-- The rank-one achievability statement for an arbitrary normalized family
of pure states, including every unitary orbit. The channels depend only on
the ambient dimension and tensor length, and have exactly zero error. -/
theorem theorem1_pure_achievability {d : ℕ} (s : FixedSpectrum d 1)
    {G : Type*} (z : G → Fin d → ℂ)
    (hz : ∀ g, ∑ i, Complex.normSq (z g i) = 1) :
    Tendsto (fun n : ℕ => Real.logb 2 (Fintype.card (Occupation d n)) -
      Weyl.qmdl d 1 s.eigenvalue n) atTop (𝓝 0) ∧
    ∀ n g, (matrix n (pure (z g))).PosSemidef ∧
      (matrix n (pure (z g))).trace = 1 ∧
      traceDistance ((decoder d n).toFun
        ((encoder d n (lt_of_lt_of_le s.rank_pos s.rank_le)).toFun
          (matrix n (pure (z g))))) (matrix n (pure (z g))) = 0 := by
  refine ⟨occupation_qmdl_asymptotic s, ?_⟩
  intro n g
  obtain ⟨hpos, htrace⟩ := source_state d n (z g) (hz g)
  exact ⟨hpos, htrace, error_zero d n _ (z g)⟩

/-- The exact finite memory size of the universal pure-state code. -/
theorem pure_memory_dimension {d : ℕ} (s : FixedSpectrum d 1) (n : ℕ) :
    Fintype.card (Occupation d n) = (n + (d - 1)).choose (d - 1) :=
  card_occupation_symm d n (lt_of_lt_of_le s.rank_pos s.rank_le)

end FreeEntropy.PureTensorCompression
