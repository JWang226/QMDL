/-
Copyright (c) 2026 Free Entropy formalization contributors.
See LICENSE and NOTICE in the repository root for license and attribution.
-/

import FreeEntropy.TypicalCanonicalRows
import FreeEntropy.CanonicalCloningBounds
import FreeEntropy.AtypicalChannels

/-! Total, actual comparison channels for the physical tensor source and
the padded canonical target. Typical sectors use the constructed Cartan
channels. Every other sector uses an explicit pure-state replacement. -/
noncomputable section
open Matrix Filter
open scoped BigOperators Topology
namespace FreeEntropy.SchurWeyl
open Channels TraceDistance ExteriorRepresentation TypicalRows CasimirWeights
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
variable {d r n : ℕ}
attribute [local instance] Classical.propDecidable

/-- The fixed typical-sector forward map, with an actual CPTP fallback. -/
def typicalCartanForward (s : FixedSpectrum d r) (n : ℕ) (i : Sector d n) :
    MatrixChannel (IrrepIndex (sectorHighestOccupation i).val)
      (IrrepIndex (targetCanonicalRow s n)) := by
  classical
  exact if h : 1 ≤ n ∧ i ∈ physicalTypical s n then
    canonicalForward (sectorHighestOccupation i).val (targetCanonicalRow s n)
      (sectorWeightHighestVector_spec i).2.1 (targetNaturalRow_antitone s n)
      (typicalCanonical_increment_antitone s n h.1 _ (Finset.mem_filter.mp h.2).2)
  else AtypicalChannels.replacementChannel ⟨0, irrep_dimension_pos _⟩

/-- The fixed typical-sector reverse map, with an actual CPTP fallback. -/
def typicalCartanReverse (s : FixedSpectrum d r) (n : ℕ) (i : Sector d n) :
    MatrixChannel (IrrepIndex (targetCanonicalRow s n))
      (IrrepIndex (sectorHighestOccupation i).val) := by
  classical
  exact if h : 1 ≤ n ∧ i ∈ physicalTypical s n then
    canonicalReverse (sectorHighestOccupation i).val (targetCanonicalRow s n)
      (sectorWeightHighestVector_spec i).2.1 (targetNaturalRow_antitone s n)
      (typicalCanonical_increment_antitone s n h.1 _ (Finset.mem_filter.mp h.2).2)
  else AtypicalChannels.replacementChannel ⟨0, irrep_dimension_pos _⟩

theorem typicalCartanForward_of_mem (s : FixedSpectrum d r) (n : ℕ) (hn : 1 ≤ n)
    (i : Sector d n) (hi : i ∈ physicalTypical s n) :
    typicalCartanForward s n i =
    canonicalForward (sectorHighestOccupation i).val (targetCanonicalRow s n)
      (sectorWeightHighestVector_spec i).2.1 (targetNaturalRow_antitone s n)
      (typicalCanonical_increment_antitone s n hn _ (Finset.mem_filter.mp hi).2) := by
  classical
  simp only [typicalCartanForward, dif_pos (show 1 ≤ n ∧ i ∈ physicalTypical s n from ⟨hn, hi⟩)]

theorem typicalCartanReverse_of_mem (s : FixedSpectrum d r) (n : ℕ) (hn : 1 ≤ n)
    (i : Sector d n) (hi : i ∈ physicalTypical s n) :
    typicalCartanReverse s n i =
    canonicalReverse (sectorHighestOccupation i).val (targetCanonicalRow s n)
      (sectorWeightHighestVector_spec i).2.1 (targetNaturalRow_antitone s n)
      (typicalCanonical_increment_antitone s n hn _ (Finset.mem_filter.mp hi).2) := by
  classical
  simp only [typicalCartanReverse, dif_pos (show 1 ≤ n ∧ i ∈ physicalTypical s n from ⟨hn, hi⟩)]

/-- Source-to-memory comparison on the literal tensor word space. -/
def mixedEncoder (s : FixedSpectrum d r) (n : ℕ) :
    MatrixChannel (Fin n → Fin d) (IrrepIndex (targetCanonicalRow s n)) :=
  physicalOrbitEncoder (typicalCartanForward s n)

/-- Memory-to-source comparison, restoring the actual physical sector law. -/
def mixedDecoder (s : FixedSpectrum d r) (n : ℕ) :
    MatrixChannel (IrrepIndex (targetCanonicalRow s n)) (Fin n → Fin d) :=
  physicalOrbitDecoder s n (typicalCartanReverse s n)

/-- The fixed constant in the uniform comparison error. -/
def mixedComparisonConstant (s : FixedSpectrum d r) (hd : 2 ≤ d) : ℝ :=
  2 * Theorem2.cloningConstant d r s.qx * ((r : ℝ) * (3 * r + 2)) / minimumGap s hd

theorem mixedComparisonConstant_nonneg (s : FixedSpectrum d r) (hd : 2 ≤ d) :
    0 ≤ mixedComparisonConstant s hd := by
  have hg := minimumGap_pos s hd
  have hK := Theorem2.cloningConstant_nonneg d r s.qx s.qx_nonneg s.qx_lt_one
  unfold mixedComparisonConstant
  positivity

/-- A single envelope for both physical comparison directions. -/
def mixedComparisonError (s : FixedSpectrum d r) (hd : 2 ≤ d) (n : ℕ) : ℝ :=
  mixedComparisonConstant s hd * Weyl.errorScale n +
    Concentration.tailBound (concentrationExponent d + d) n

theorem mixedComparisonError_nonneg (s : FixedSpectrum d r) (hd : 2 ≤ d)
    (n : ℕ) (hn : 2 ≤ n) : 0 ≤ mixedComparisonError s hd n := by
  have hc := mixedComparisonConstant_nonneg s hd
  have he : 0 ≤ Weyl.errorScale n := by
    unfold Weyl.errorScale
    exact div_nonneg (Real.logb_nonneg (by norm_num) (by exact_mod_cast (show 1 ≤ n by omega)))
      (Real.sqrt_nonneg _)
  unfold mixedComparisonError Concentration.tailBound
  positivity

theorem mixedComparisonError_isBigO (s : FixedSpectrum d r) (hd : 2 ≤ d) :
    Asymptotics.IsBigO atTop (mixedComparisonError s hd) Weyl.errorScale := by
  apply Asymptotics.IsBigO.of_bound (mixedComparisonConstant s hd + 1)
  filter_upwards [Concentration.tailBound_eventually_le_errorScale (concentrationExponent d + d),
    eventually_ge_atTop 2] with n ht hn
  have he : 0 ≤ Weyl.errorScale n := by
    unfold Weyl.errorScale
    exact div_nonneg (Real.logb_nonneg (by norm_num) (by exact_mod_cast (show 1 ≤ n by omega)))
      (Real.sqrt_nonneg _)
  rw [Real.norm_eq_abs, abs_of_nonneg (mixedComparisonError_nonneg s hd n hn),
    Real.norm_eq_abs, abs_of_nonneg he]
  change mixedComparisonConstant s hd * Weyl.errorScale n + _ ≤ _
  change Concentration.tailBound _ n ≤ Weyl.errorScale n at ht
  nlinarith

/-- Before conjugating the orbit, every actual typical-sector channel has
uniformly vanishing error, derived only from the fixed spectrum. -/
theorem typicalCartan_diagonal_error_eventually (s : FixedSpectrum d r) (hd : 2 ≤ d) : ∀ᶠ n in atTop, ∀ i ∈ physicalTypical s n,
    traceDistance ((typicalCartanForward s n i).toFun
        ((canonicalWeightModel (sectorHighestOccupation i).val).relativeState
          (fun j => s.adjacentRatio j.val)))
      ((canonicalWeightModel (targetCanonicalRow s n)).relativeState
        (fun j => s.adjacentRatio j.val)) ≤ mixedComparisonConstant s hd * Weyl.errorScale n ∧
    traceDistance ((typicalCartanReverse s n i).toFun
        ((canonicalWeightModel (targetCanonicalRow s n)).relativeState
          (fun j => s.adjacentRatio j.val)))
      ((canonicalWeightModel (sectorHighestOccupation i).val).relativeState
        (fun j => s.adjacentRatio j.val)) ≤ mixedComparisonConstant s hd * Weyl.errorScale n := by
  classical
  filter_upwards [typicalCanonical_eventually_minimumGap s hd, eventually_ge_atTop 2] with n hg hn
  intro i hi
  have ht := (Finset.mem_filter.mp hi).2
  have hmu := (sectorWeightHighestVector_spec i).2.1
  have hinc := typicalCanonical_increment_antitone s n (by omega) _ ht
  have hzero : ∀ j : Fin d, r ≤ j.val → targetCanonicalRow s n j = (sectorHighestOccupation i).val j := by
    intro j hj
    rw [targetCanonicalRow_supported s n j hj, typicalCanonical_supported s n _ ht j hj]
  have hb : 0 ≤ (n : ℝ) * minimumGap s hd / 2 := by
    exact div_nonneg (mul_nonneg (Nat.cast_nonneg _) (minimumGap_pos s hd).le) (by norm_num)
  have he := canonical_cloning_accuracy_bounds s hd (sectorHighestOccupation i).val (targetCanonicalRow s n)
    hmu (targetNaturalRow_antitone s n) hinc hzero
    (differenceNorm (sectorHighestOccupation i).val (targetCanonicalRow s n))
    (minimumRowGap (sectorHighestOccupation i).val r hd s.rank_pos)
    ((n : ℝ) * minimumGap s hd / 2)
    hb (hg _ hmu ht)
    (by rw [differenceNorm_cast])
    (minimumRowGap_cast_le _ hmu r hd s.rank_pos)
  have hK := Theorem2.cloningConstant_nonneg d r s.qx s.qx_nonneg s.qx_lt_one
  have hbound := typicalCanonical_envelope_le s hd _ hK n hn _ ht
  rw [differenceNorm_cast] at he
  rw [typicalCartanForward_of_mem s n (by omega) i hi,
    typicalCartanReverse_of_mem s n (by omega) i hi]
  exact ⟨he.1.trans hbound, he.2.trans hbound⟩

end FreeEntropy.SchurWeyl
