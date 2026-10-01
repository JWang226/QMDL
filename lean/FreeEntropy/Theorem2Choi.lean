/-
Copyright (c) 2026 Free Entropy formalization contributors.
See LICENSE and NOTICE in the repository root for license and attribution.
-/

import FreeEntropy.CanonicalChoi
import FreeEntropy.CanonicalReverseChoi
import FreeEntropy.ReverseChoiRepresentation
import FreeEntropy.ReverseChoiMultiplicity
import FreeEntropy.ChoiContraction
import FreeEntropy.Theorem2Canonical

/-! Theorem 2 using the manuscript's original normalized Choi-projector
contraction. The relevant PRV projector and its uniqueness are proved in
`CanonicalChoi`, rather than supplied as hypotheses. -/
noncomputable section
open Matrix
open scoped Kronecker
namespace FreeEntropy.ExteriorRepresentation
open CartanChoi TraceDistance
set_option backward.isDefEq.respectTransparency false
variable {d r : ℕ}

/-- The literal forward definition `Tr_mu[(d_mu/d_omega) Pi_omega (Xᵀ⊗I)]`. -/
def prvForward (mu nu : Fin d → ℕ) (hmu : Antitone mu) (hnu : Antitone nu)
    (hinc : Antitone (fun i => (nu i : ℝ) - (mu i : ℝ)))
    (X : Matrix (IrrepIndex mu) (IrrepIndex mu) ℂ) :
    Matrix (IrrepIndex nu) (IrrepIndex nu) ℂ :=
  partialTraceInput
    ((((Fintype.card (IrrepIndex mu) : ℝ) /
      Fintype.card (IrrepIndex (auxiliaryRow mu nu))) •
      canonicalChoiProjector mu nu hmu hnu hinc) * (X.transpose ⊗ₖ 1))

/-- The original Choi definition and the constructed CPTP map agree on all
matrices, including when the highest rows coincide. -/
theorem prvForward_eq (mu nu : Fin d → ℕ) (hmu : Antitone mu) (hnu : Antitone nu)
    (hinc : Antitone (fun i => (nu i : ℝ) - (mu i : ℝ))) (hd : 0 < d)
    (X : Matrix (IrrepIndex mu) (IrrepIndex mu) ℂ) :
    prvForward mu nu hmu hnu hinc X = (canonicalForward mu nu hmu hnu hinc).toFun X := by
  rw [prvForward, ← choiMap_eq_partialTraceInput]
  exact canonicalForward_choiMap mu nu hmu hnu hinc hd X

/-- The literal reverse definition from its conjugate-dual PRV projector. -/
def prvReverse (mu nu : Fin d → ℕ) (hmu : Antitone mu) (hnu : Antitone nu)
    (hinc : Antitone (fun i => (nu i : ℝ) - (mu i : ℝ)))
    (Y : Matrix (IrrepIndex nu) (IrrepIndex nu) ℂ) :
    Matrix (IrrepIndex mu) (IrrepIndex mu) ℂ :=
  partialTraceInput
    ((((Fintype.card (IrrepIndex nu) : ℝ) /
      Fintype.card (IrrepIndex (auxiliaryRow mu nu))) •
      canonicalReverseChoiProjector mu nu hmu hnu hinc) * (Y.transpose ⊗ₖ 1))

theorem prvReverse_eq (mu nu : Fin d → ℕ) (hmu : Antitone mu) (hnu : Antitone nu)
    (hinc : Antitone (fun i => (nu i : ℝ) - (mu i : ℝ))) (hd : 0 < d)
    (Y : Matrix (IrrepIndex nu) (IrrepIndex nu) ℂ) :
    prvReverse mu nu hmu hnu hinc Y = (canonicalReverse mu nu hmu hnu hinc).toFun Y := by
  rw [prvReverse, ← choiMap_eq_partialTraceInput]
  exact canonicalReverse_choiMap mu nu hmu hnu hinc hd Y

/-- Both original projector formulas are actual CPTP channels; no
positivity or trace-preservation hypotheses are supplied. -/
theorem prv_maps_are_channels (mu nu : Fin d → ℕ)
    (hmu : Antitone mu) (hnu : Antitone nu)
    (hinc : Antitone (fun i => (nu i : ℝ) - (mu i : ℝ))) (hd : 0 < d) :
    ∃ F : Channels.MatrixChannel (IrrepIndex mu) (IrrepIndex nu),
      ∃ R : Channels.MatrixChannel (IrrepIndex nu) (IrrepIndex mu),
        F.toFun = prvForward mu nu hmu hnu hinc ∧
        R.toFun = prvReverse mu nu hmu hnu hinc := by
  refine ⟨canonicalForward mu nu hmu hnu hinc, canonicalReverse mu nu hmu hnu hinc, ?_, ?_⟩
  · funext X
    exact (prvForward_eq mu nu hmu hnu hinc hd X).symm
  · funext Y
    exact (prvReverse_eq mu nu hmu hnu hinc hd Y).symm

/-- **Theorem 2 in its original Choi-projector formulation.** Both
normalized PRV projectors, their highest-weight components and multiplicity
one are constructed. The exact original partial-trace formulas equal the
actual CPTP maps, and satisfy both errors for every unknown eigenbasis. -/
theorem theorem2_cloning_accuracy_choi
    (s : FixedSpectrum d r) (hd : 2 ≤ d)
    (mu nu : Fin d → ℕ) (hmu : Antitone mu) (hnu : Antitone nu)
    (hmu_support : ∀ i : Fin d, r ≤ i.val → mu i = 0)
    (hnu_support : ∀ i : Fin d, r ≤ i.val → nu i = 0)
    (hinc : Antitone (fun i => (nu i : ℝ) - (mu i : ℝ)))
    (U : Matrix.unitaryGroup (Fin d) ℂ) :
    traceDistance (prvForward mu nu hmu hnu hinc (canonicalOrbitState s mu U))
      (canonicalOrbitState s nu U) ≤
        Theorem2.cloningConstant d r s.qx * (differenceNorm mu nu : ℝ) /
          ((minimumRowGap mu r hd s.rank_pos : ℝ) + 1) ∧
    traceDistance (prvReverse mu nu hmu hnu hinc (canonicalOrbitState s nu U))
      (canonicalOrbitState s mu U) ≤
        Theorem2.cloningConstant d r s.qx * (differenceNorm mu nu : ℝ) /
          ((minimumRowGap mu r hd s.rank_pos : ℝ) + 1) := by
  rw [prvForward_eq mu nu hmu hnu hinc (by omega),
    prvReverse_eq mu nu hmu hnu hinc (by omega)]
  exact theorem2_cloning_accuracy s hd mu nu hmu hnu hmu_support hnu_support hinc U

end FreeEntropy.ExteriorRepresentation
