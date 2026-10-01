/-
Copyright (c) 2026 Free Entropy formalization contributors.
See LICENSE and NOTICE in the repository root for license and attribution.
-/

import FreeEntropy.Theorem2GT
import FreeEntropy.GTRankSupport

/-!
# Canonical finite GT weight support

The offset set is constructed from the actual finite pattern type. Its
validity, highest-weight membership, and vanishing multiplicities outside
the set are proved. Taking the union for two highest weights removes the
finite-support input from the concrete Theorem 2 statement.
-/

noncomputable section
open scoped BigOperators

namespace FreeEntropy.GelfandTsetlin

/-- The exact set of offsets realized by actual GT patterns. -/
def supportedCuts {r : ℕ} (μ : Fin r → ℤ) : Finset (ℕ → ℕ) := by
  classical
  exact Finset.univ.image (fun P : Pattern μ => KostantCounting.typeAOffset r (drops P))

theorem supportedCuts_valid {r : ℕ} (μ : Fin r → ℤ) (δ : ℕ → ℕ)
    (hδ : δ ∈ supportedCuts μ) : ValidCuts r δ := by
  classical
  obtain ⟨P, _, rfl⟩ := Finset.mem_image.mp hδ
  exact typeAOffset_valid r (drops P)

theorem zero_mem_supportedCuts {r : ℕ} (μ : Fin r → ℤ) (hμ : Dominant μ) :
    (0 : ℕ → ℕ) ∈ supportedCuts μ := by
  classical
  apply Finset.mem_image.mpr
  refine ⟨highestPattern μ hμ, Finset.mem_univ _, ?_⟩
  rw [drops_highestPattern]
  ext k
  simp [KostantCounting.typeAOffset]

theorem mem_supportedCuts_iff {r : ℕ} (μ : Fin r → ℤ) (δ : ℕ → ℕ) :
    δ ∈ supportedCuts μ ↔ 0 < cutMultiplicity μ δ := by
  classical
  rw [cutMultiplicity, Fintype.card_pos_iff]
  constructor
  · intro h
    obtain ⟨P, _, hP⟩ := Finset.mem_image.mp h
    exact ⟨⟨P, hP⟩⟩
  · rintro ⟨P⟩
    exact Finset.mem_image.mpr ⟨P.val, Finset.mem_univ _, P.property⟩

theorem cutMultiplicity_eq_zero_of_not_mem {r : ℕ} (μ : Fin r → ℤ) (δ : ℕ → ℕ)
    (hδ : δ ∉ supportedCuts μ) : cutMultiplicity μ δ = 0 := by
  have h := mt (mem_supportedCuts_iff μ δ).mpr hδ
  omega

/-- No ordinary GT weight at a valid cut offset is lost outside the constructed support. -/
theorem multiplicity_eq_zero_of_not_mem {r : ℕ} (μ : Fin r → ℤ) (δ : ℕ → ℕ)
    (hv : ValidCuts r δ) (hδ : δ ∉ supportedCuts μ) :
    multiplicity μ (coordinateOffset r δ) = 0 := by
  rw [← cutMultiplicity_eq_multiplicity μ δ hv]
  exact cutMultiplicity_eq_zero_of_not_mem μ δ hδ

/-- A common finite index set containing the complete supports of both representations. -/
def commonCuts {r : ℕ} (μ ω : Fin r → ℤ) : Finset (ℕ → ℕ) := by
  classical
  exact supportedCuts μ ∪ supportedCuts (μ + ω)

theorem commonCuts_valid {r : ℕ} (μ ω : Fin r → ℤ) (δ : ℕ → ℕ)
    (hδ : δ ∈ commonCuts μ ω) : ValidCuts r δ := by
  classical
  rcases Finset.mem_union.mp hδ with h | h
  · exact supportedCuts_valid μ δ h
  · exact supportedCuts_valid (μ + ω) δ h

theorem zero_mem_commonCuts {r : ℕ} (μ ω : Fin r → ℤ) (hμ : Dominant μ) :
    (0 : ℕ → ℕ) ∈ commonCuts μ ω := by
  classical
  exact Finset.mem_union_left _ (zero_mem_supportedCuts μ hμ)

theorem multiplicities_eq_zero_outside_commonCuts {r : ℕ} (μ ω : Fin r → ℤ)
    (δ : ℕ → ℕ) (hv : ValidCuts r δ) (hδ : δ ∉ commonCuts μ ω) :
    multiplicity μ (coordinateOffset r δ) = 0 ∧
      multiplicity (μ + ω) (coordinateOffset r δ) = 0 := by
  classical
  constructor
  · apply multiplicity_eq_zero_of_not_mem μ δ hv
    exact fun h => hδ (Finset.mem_union_left _ h)
  · apply multiplicity_eq_zero_of_not_mem (μ + ω) δ hv
    exact fun h => hδ (Finset.mem_union_right _ h)

end FreeEntropy.GelfandTsetlin

namespace FreeEntropy.Theorem2GT

open GelfandTsetlin KostantCounting CloningMatrices TraceDistance

variable {H K : Type*} [Fintype H] [DecidableEq H] [Fintype K] [DecidableEq K]

/-- The canonical-support version of Theorem 2: no finite offset set or
support assumptions are supplied, and all supported GT weights are included. -/
theorem theorem2_gt_canonical_from_integer_rows
    (d r g : ℕ) (μ ω : ℕ → ℤ) (ratio : ℕ → ℝ) (b q : ℝ)
    (R : TraceCloning.TraceBlockRealization (commonCuts (rankRow r μ) (rankRow r ω))
      (gtMultiplicity (rankRow r μ)) (gtMultiplicity (rankRow r μ + rankRow r ω))
      (gtCoefficient (commonCuts (rankRow r μ) (rankRow r ω)) (rankRow r μ) ratio)
      (gtCoefficient (commonCuts (rankRow r μ) (rankRow r ω)) (rankRow r μ + rankRow r ω) ratio)
      (fun δ => min 1 (2 * (offsetDepth r δ : ℝ) * (rowDistance d ω : ℝ) /
        ((g : ℝ) + 2))) (weylRatio d μ ω) H K)
    (hrank : 2 ≤ r) (hrd : r ≤ d)
    (hμ : ∀ i j, i < j → j < d → μ j ≤ μ i)
    (hω : ∀ i j, i < j → j < d → ω j ≤ ω i)
    (hzero : ∀ i, r ≤ i → i < d → ω i = 0)
    (hratio : ∀ j < r - 1, 0 ≤ ratio j) (hbound : ∀ j < r - 1, ratio j ≤ q)
    (hq : 0 ≤ q) (hq1 : q < 1) (hb : 0 ≤ b) (hbg : b ≤ (g : ℝ))
    (hgap : HasGap (rankRow r μ) g)
    (hactive : ∀ i, i < r → i + 1 < d → b ≤ (μ i : ℝ) - (μ (i + 1) : ℝ)) :
    traceDistance (R.forward.toFun (mixture (commonCuts (rankRow r μ) (rankRow r ω))
        (gtCoefficient (commonCuts (rankRow r μ) (rankRow r ω)) (rankRow r μ) ratio) R.Pμ))
        (mixture (commonCuts (rankRow r μ) (rankRow r ω))
          (gtCoefficient (commonCuts (rankRow r μ) (rankRow r ω))
            (rankRow r μ + rankRow r ω) ratio) R.Pν) ≤
        Theorem2.cloningConstant d r q * (rowDistance d ω : ℝ) / (b + 1) ∧
    traceDistance (R.reverse.toFun (mixture (commonCuts (rankRow r μ) (rankRow r ω))
        (gtCoefficient (commonCuts (rankRow r μ) (rankRow r ω))
          (rankRow r μ + rankRow r ω) ratio) R.Pν))
        (mixture (commonCuts (rankRow r μ) (rankRow r ω))
          (gtCoefficient (commonCuts (rankRow r μ) (rankRow r ω)) (rankRow r μ) ratio) R.Pμ) ≤
        Theorem2.cloningConstant d r q * (rowDistance d ω : ℝ) / (b + 1) :=
  theorem2_gt_from_integer_rows d r g (commonCuts (rankRow r μ) (rankRow r ω))
    μ ω ratio b q R hrank hrd hμ hω hzero
    (commonCuts_valid _ _) (zero_mem_commonCuts _ _ (rankRow_dominant hrd μ hμ))
    hratio hbound hq hq1 hb hbg hgap hactive

end FreeEntropy.Theorem2GT
