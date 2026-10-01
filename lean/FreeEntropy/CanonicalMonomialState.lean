/-
Copyright (c) 2026 Free Entropy formalization contributors.
See LICENSE and NOTICE in the repository root for license and attribution.
-/

import FreeEntropy.PhysicalCanonicalSector
import FreeEntropy.CyclicWeightStates
import FreeEntropy.SpectrumBounds

/-! The literal normalized physical occupation monomials coincide with the
relative simple-root state. All factorizations permit zero spectral ratios,
so the result includes rank-deficient spectra. -/
noncomputable section
open scoped BigOperators
open Matrix
namespace FreeEntropy.CanonicalMonomials
open CasimirWeights CartanLieCloning
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
variable {d r : ℕ}

/-- A zero-safe prefix product of adjacent ratios. -/
def prefixProduct (q : Fin (d - 1) → ℝ) (i : ℕ) : ℝ := ∏ j with j.val < i, q j

theorem prefixProduct_succ (q : Fin (d - 1) → ℝ) (i : ℕ) (hi : i < d - 1) :
    prefixProduct q (i + 1) = prefixProduct q i * q ⟨i, hi⟩ := by
  classical
  have hs : Finset.univ.filter (fun j : Fin (d - 1) => j.val < i + 1) =
      insert ⟨i, hi⟩ (Finset.univ.filter (fun j : Fin (d - 1) => j.val < i)) := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Fin.ext_iff]
    omega
  unfold prefixProduct
  rw [hs, Finset.prod_insert (by simp)]
  exact mul_comm _ _

theorem spectrum_recurrence (s : FixedSpectrum d r) (i : ℕ) (hi : i + 1 < d) :
    s.eigenvalue (i + 1) = s.eigenvalue i * s.adjacentRatio i := by
  by_cases hp : i + 1 < r
  · rw [FixedSpectrum.adjacentRatio, if_pos hp]
    exact (mul_div_cancel₀ _ (s.positive i (by omega)).ne').symm
  · rw [FixedSpectrum.adjacentRatio, if_neg hp, mul_zero]
    exact s.zero_padded (i + 1) (by omega) hi

theorem spectrum_prefixProduct (s : FixedSpectrum d r) (i : ℕ) (hi : i < d) :
    s.eigenvalue i = s.eigenvalue 0 * prefixProduct (d := d) (fun j => s.adjacentRatio j.val) i := by
  induction i with
  | zero => simp [prefixProduct]
  | succ i ih =>
    rw [spectrum_recurrence s i hi, ih (by omega), prefixProduct_succ _ i (by omega)]
    exact mul_assoc _ _ _

def suffix (w : Fin d → ℕ) (j : Fin (d - 1)) : ℕ := ∑ i with j.val < i.val, w i

/-- Each adjacent ratio occurs with the suffix sum of occupation exponents. -/
theorem monomial_factor (s : FixedSpectrum d r) (w : Fin d → ℕ) :
    (∏ i : Fin d, s.eigenvalue i.val ^ w i) =
      s.eigenvalue 0 ^ (∑ i, w i) * ∏ j : Fin (d - 1), s.adjacentRatio j.val ^ suffix w j := by
  classical
  simp_rw [spectrum_prefixProduct s _ (Fin.isLt _), mul_pow]
  rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
  congr 1
  simp only [prefixProduct, Finset.prod_filter, ← Finset.prod_pow]
  rw [Finset.prod_comm]
  apply Finset.prod_congr rfl
  intro j _
  simp only [suffix, Finset.sum_filter, ← Finset.prod_pow_eq_pow_sum]
  apply Finset.prod_congr rfl
  intro i _
  split_ifs <;> simp

/-- The integral cone gives an exact suffix-sum identity, including weights
outside the positive spectral support. -/
theorem suffix_eq_of_cone (mu w : Fin d → ℕ) (c : Fin (d - 1) → ℕ)
    (hc : (fun i => (mu i : ℝ)) - (fun i => (w i : ℝ)) = offset c)
    (ht : ∑ i, mu i = ∑ i, w i) (j : Fin (d - 1)) :
    suffix w j = suffix mu j + c j := by
  classical
  have hp := CasimirDecomposition.prefix_offset c j
  rw [← hc] at hp
  simp only [Pi.sub_apply, Finset.sum_sub_distrib] at hp
  have hm : (∑ i : Fin d with i.val ≤ j.val, (mu i : ℝ)) +
      (suffix mu j : ℝ) = ∑ i : Fin d, (mu i : ℝ) := by
    simp only [suffix, Nat.cast_sum]
    simpa only [not_le] using Finset.sum_filter_add_sum_filter_not
      (Finset.univ : Finset (Fin d)) (fun i => i.val ≤ j.val) (fun i => (mu i : ℝ))
  have hw : (∑ i : Fin d with i.val ≤ j.val, (w i : ℝ)) +
      (suffix w j : ℝ) = ∑ i : Fin d, (w i : ℝ) := by
    simp only [suffix, Nat.cast_sum]
    simpa only [not_le] using Finset.sum_filter_add_sum_filter_not
      (Finset.univ : Finset (Fin d)) (fun i => i.val ≤ j.val) (fun i => (w i : ℝ))
  have ht' : (∑ i, (mu i : ℝ)) = ∑ i, (w i : ℝ) := by exact_mod_cast ht
  have he : (suffix w j : ℝ) = (suffix mu j : ℝ) + c j := by linarith
  exact_mod_cast he

/-- The occupation monomial is its highest monomial times the root-deficit
monomial, proved without dividing by any spectral eigenvalue. -/
theorem monomial_relative (s : FixedSpectrum d r) (mu w : Fin d → ℕ)
    (c : Fin (d - 1) → ℕ)
    (hc : (fun i => (mu i : ℝ)) - (fun i => (w i : ℝ)) = offset c)
    (ht : ∑ i, mu i = ∑ i, w i) :
    (∏ i : Fin d, s.eigenvalue i.val ^ w i) =
      (∏ i : Fin d, s.eigenvalue i.val ^ mu i) *
        rootWeightMonomial (fun j => s.adjacentRatio j.val) c := by
  rw [monomial_factor s w, monomial_factor s mu, ht]
  simp_rw [suffix_eq_of_cone mu w c hc ht, pow_add]
  rw [Finset.prod_mul_distrib]
  exact (mul_assoc _ _ _).symm

end FreeEntropy.CanonicalMonomials

namespace FreeEntropy.CanonicalMonomials
open CartanLieCloning ExteriorRepresentation
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
variable {d r : ℕ}

theorem canonical_monomial_relative (s : FixedSpectrum d r) (mu : Fin d → ℕ)
    (hmu : Antitone mu) (a : IrrepIndex mu) :
    (∏ i : Fin d, s.eigenvalue i.val ^ canonicalWeight mu a i) =
      (∏ i : Fin d, s.eigenvalue i.val ^ mu i) *
        (canonicalWeightModel mu).relativeWeight (fun j => s.adjacentRatio j.val) a := by
  apply monomial_relative s mu (canonicalWeight mu a) ((canonicalWeightModel mu).weightCoeff a)
  · have h := (canonicalWeightModel mu).weight_cone a
    rw [canonicalWeightModel_row mu hmu, canonicalWeight_spec mu a] at h
    exact h
  · exact (canonicalWeight_sum mu hmu a).symm

/-- A supported highest occupation has strictly positive physical monomial. -/
theorem highest_monomial_pos (s : FixedSpectrum d r) (mu : Fin d → ℕ)
    (hsupp : ∀ i, r ≤ i.val → mu i = 0) :
    0 < ∏ i : Fin d, s.eigenvalue i.val ^ mu i := by
  apply Finset.prod_pos
  intro i _
  by_cases hi : i.val < r
  · exact pow_pos (s.positive i.val hi) _
  · rw [hsupp i (Nat.le_of_not_gt hi), pow_zero]
    exact zero_lt_one

variable {A : Type*} [Fintype A] [DecidableEq A] [Nonempty A]

/-- A common nonzero real factor cancels in literal block normalization. -/
theorem normalized_diagonal_factor (k : ℝ) (hk : k ≠ 0) (w : A → ℝ)
    (hZ : ∑ a, w a ≠ 0) :
    SchurWeyl.normalizedBlock (Matrix.diagonal (fun a => ((k * w a : ℝ) : ℂ))) =
      Matrix.diagonal (fun a => ((w a / ∑ b, w b : ℝ) : ℂ)) := by
  have ht : OrbitMemory.tr (Matrix.diagonal (fun a => ((k * w a : ℝ) : ℂ))) = k * ∑ a, w a := by
    simp [OrbitMemory.tr, Matrix.trace_diagonal, ← Finset.mul_sum]
  rw [SchurWeyl.normalizedBlock, ht, if_neg (mul_ne_zero hk hZ)]
  apply Matrix.ext
  intro a b
  by_cases hab : a = b
  · subst b
    simp only [Matrix.smul_apply, Matrix.diagonal_apply_eq, Complex.real_smul]
    rw [← Complex.ofReal_mul]
    congr 1
    field_simp
  · simp [Matrix.smul_apply, Matrix.diagonal_apply_ne _ hab, hab]

end FreeEntropy.CanonicalMonomials

namespace FreeEntropy.SchurWeyl
open CartanLieCloning ExteriorRepresentation CanonicalMonomials
set_option backward.isDefEq.respectTransparency false
variable {d r : ℕ}

/-- The actual normalized physical monomial state is exactly the relative
simple-root state, including spectra with zero eigenvalues. -/
theorem canonicalMonomialState_eq_relativeState (s : FixedSpectrum d r)
    (mu : Fin d → ℕ) (hmu : Antitone mu)
    (hsupp : ∀ i, r ≤ i.val → mu i = 0) :
    canonicalMonomialState mu (fun i => (s.eigenvalue i.val : ℂ)) =
      (canonicalWeightModel mu).relativeState (fun j => s.adjacentRatio j.val) := by
  letI : Nonempty (IrrepIndex mu) := Fin.pos_iff_nonempty.mp (irrep_dimension_pos mu)
  have hw (a : IrrepIndex mu) :
      (∏ i : Fin d, (s.eigenvalue i.val : ℂ) ^ canonicalWeight mu a i) =
        (((∏ i : Fin d, s.eigenvalue i.val ^ mu i) *
          (canonicalWeightModel mu).relativeWeight (fun j => s.adjacentRatio j.val) a : ℝ) : ℂ) := by
    rw [← canonical_monomial_relative s mu hmu a]
    simp only [Complex.ofReal_prod, Complex.ofReal_pow]
  have hZ : (canonicalWeightModel mu).relativeNormalizer (fun j => s.adjacentRatio j.val) ≠ 0 :=
    ne_of_gt (lt_of_lt_of_le zero_lt_one ((canonicalWeightModel mu).relativeNormalizer_ge_one
      (fun j => s.adjacentRatio j.val) (fun j => s.adjacentRatio_nonneg j.val)))
  unfold canonicalMonomialState
  simp_rw [hw]
  exact normalized_diagonal_factor _ (highest_monomial_pos s mu hsupp).ne' _ hZ

end FreeEntropy.SchurWeyl
