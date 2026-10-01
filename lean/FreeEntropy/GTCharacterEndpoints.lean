/-
Copyright (c) 2026 Free Entropy formalization contributors.
See LICENSE and NOTICE in the repository root for license and attribution.
-/

import FreeEntropy.GTDimensionFormula
import FreeEntropy.SchurProbabilityConcentration

/-!
# General achievability with proved GT dimension and concentration

The memory size is the actual cardinality of the padded GT basis, and the
concentration estimate follows from the exact standard-tableau/GT-character
formula. Neither a Weyl dimension identity nor a pointwise probability
inequality is supplied to this endpoint. Physical Schur source realization
and local cloning channels remain explicit through the code and its formula.
-/

noncomputable section
open Filter
open scoped Topology

namespace FreeEntropy.SchurAchievability
open TraceDistance

/-- General-rank achievability for the actual padded GT memory, with the
entire probability bound derived from the exact combinatorial formula. -/
theorem theorem1_schur_achievability_gt_tableau {d r : ℕ}
    (s : FixedSpectrum d r) (hd : 2 ≤ d)
    (code : ∀ n, Code (GTDimension.targetDimension s n)) (K : ℝ) (hK : 0 ≤ K)
    (hformulas : ∀ᶠ n in atTop, (code n).TableauGTFormula s n)
    (hf : ∀ᶠ n in atTop, ∀ i ∈ (code n).typical,
      traceDistance (((code n).forward i).toFun ((code n).state i)) (code n).target ≤
        cloningEnvelope s hd K n ((code n).row i))
    (hr : ∀ᶠ n in atTop, ∀ i ∈ (code n).typical,
      traceDistance (((code n).reverse i).toFun (code n).target) ((code n).state i) ≤
        cloningEnvelope s hd K n ((code n).row i)) :
    Tendsto (fun n => Real.logb 2 (GTDimension.targetDimension s n) -
      Weyl.qmdl d r s.eigenvalue n) atTop (𝓝 0) ∧
      Asymptotics.IsBigO atTop (fun n => (code n).error) Weyl.errorScale ∧
      Tendsto (fun n => (code n).error) atTop (𝓝 0) :=
  theorem1_schur_achievability_of_tableau_gt s hd (GTDimension.targetDimension s)
    code K hK (Eventually.of_forall (GTDimension.targetDimension_weyl s)) hformulas hf hr

/-- The actual code's atypical mass is controlled at every nontrivial block
length for which its exact tableau/GT probability formula is established. -/
theorem actual_gt_code_tail_bound {d r : ℕ} (s : FixedSpectrum d r) (n : ℕ)
    (hn : 2 ≤ n) (code : Code (GTDimension.targetDimension s n))
    (hformula : code.TableauGTFormula s n) :
    code.tail ≤ Concentration.tailBound (r.choose 2 + r) n :=
  code.tail_le_from_tableau_gt s n hn hformula

end FreeEntropy.SchurAchievability
