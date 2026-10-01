/-
Copyright (c) 2026 Free Entropy formalization contributors.
See LICENSE and NOTICE in the repository root for license and attribution.
-/

import FreeEntropy.OccupationForward
import FreeEntropy.OccupationIrreducible

/-!
# Werner cloning on the genuine symmetric-power representation

Both channels are concrete CPTP maps. Their Cartan embedding, the unitary
action, its irreducibility, and the dimension normalization are all proved.
The finite pure-state error bounds have no representation hypotheses.
-/
noncomputable section
open scoped BigOperators Matrix Kronecker ComplexOrder MatrixOrder
open Matrix
namespace FreeEntropy.OccupationCloning
open Occupation OccupationSplit CartanChannel TraceDistance
set_option backward.isDefEq.respectTransparency false

/-- The actual Werner channel from n to n+m symmetric copies. -/
def forward (d n m : ℕ) (hd : 0 < d) :
    Channels.MatrixChannel (Occupation d n) (Occupation d (n + m)) := by
  letI := unitaryRepresentation_irreducible d n hd
  letI : Nonempty (Occupation d n) := ⟨PureTensorCompression.defaultOccupation d n hd⟩
  letI : Nonempty (Occupation d (n + m)) := ⟨PureTensorCompression.defaultOccupation d (n + m) hd⟩
  exact CartanBalance.cartanChannelOfIrreducible
    (unitaryRepresentation d n) (unitaryRepresentation d m) (unitaryRepresentation d (n + m))
    (unitaryRepresentation_unitary d n) (unitaryRepresentation_unitary d m)
    (unitaryRepresentation_unitary d (n + m)) split split_isometry
    (fun U => split_intertwines U.val)

theorem forward_apply (d n m : ℕ) (hd : 0 < d)
    (X : Matrix (Occupation d n) (Occupation d n) ℂ) :
    (forward d n m hd).toFun X =
      sectorMap (Fintype.card (Occupation d n)) (Fintype.card (Occupation d (n + m))) split X := by
  letI := unitaryRepresentation_irreducible d n hd
  letI : Nonempty (Occupation d n) := ⟨PureTensorCompression.defaultOccupation d n hd⟩
  letI : Nonempty (Occupation d (n + m)) := ⟨PureTensorCompression.defaultOccupation d (n + m) hd⟩
  apply CartanBalance.cartanChannelOfIrreducible_apply

/-- The complete rank-one cloning theorem with exact dimensions and actual
physical symmetric-power representations and channels. -/
theorem pure_cloning (d n m : ℕ) (hd : 0 < d) (z : Fin d → ℂ)
    (hz : ∑ i, Complex.normSq (z i) = 1) :
    traceDistance ((forward d n m hd).toFun (state n z)) (state (n + m) z) ≤
        1 - dimensionRatio d n m ∧
      traceDistance ((reverse d n m).toFun (state (n + m) z)) (state n z) = 0 := by
  exact ⟨forward_error_of_formula hd (forward d n m hd) (forward_apply d n m hd) z hz,
    reverse_error_zero n m z hz⟩

end FreeEntropy.OccupationCloning
