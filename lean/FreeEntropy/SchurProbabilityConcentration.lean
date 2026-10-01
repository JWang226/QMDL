/-
Copyright (c) 2026 Free Entropy formalization contributors.
See LICENSE and NOTICE in the repository root for license and attribution.
-/

import FreeEntropy.SchurProbabilityCharacter
import FreeEntropy.SchurAchievability

/-!
# Concentration from the actual tableau–GT probability formula

This bridge eliminates the pointwise relative-entropy estimate from the
Schur-code assumptions: it is proved from standard-tableau counts and the
GT polynomial character. Identifying this explicit formula with the block
probabilities of the physical tensor power remains a representation theorem.
-/
noncomputable section
open Filter
open scoped BigOperators Topology
namespace FreeEntropy.SchurAchievability
open TraceDistance
set_option backward.isDefEq.respectTransparency false

/-- Structural diagram data and the exact combinatorial probability formula.
No probability inequality or tail bound is included. -/
structure Code.TableauGTFormula {d r m : ℕ} (s : FixedSpectrum d r)
    (n : ℕ) (C : Code m) : Prop where
  row_injective : Function.Injective (fun a (i : Fin r) => C.row a i)
  row_nonneg : ∀ a i, i < r → 0 ≤ C.row a i
  row_zero : ∀ a i, r ≤ i → i < d → C.row a i = 0
  row_size : ∀ a, ∑ i : Fin r, C.row a i = (n : ℤ)
  mem_typical : ∀ a, a ∈ C.typical ↔ TypicalRows.Typical s n (C.row a)
  probability_formula : ∀ a, C.probability a = SchurProbability.schurMass
    (fun i : Fin r => (C.row a i).toNat) n (fun i : Fin r => s.eigenvalue i)

/-- The complete pointwise estimate follows from the exact character formula. -/
theorem Code.TableauGTFormula.toDiagramEstimate {d r m : ℕ} {s : FixedSpectrum d r}
    {n : ℕ} {C : Code m} (h : C.TableauGTFormula s n) (hn : 0 < n) :
    C.DiagramEstimate s n := by
  refine ⟨h.row_injective, h.row_nonneg, ?_, h.row_zero, h.row_size, h.mem_typical, ?_⟩
  · intro a i hi
    have hle := Finset.single_le_sum (f := fun j : Fin r => C.row a j)
      (fun j _ => h.row_nonneg a j j.isLt) (Finset.mem_univ (⟨i, hi⟩ : Fin r))
    simpa only [h.row_size a] using hle
  · intro a
    have hsize : ∑ i : Fin r, (C.row a i).toNat = n := by
      have he : (∑ i : Fin r, ((C.row a i).toNat : ℤ)) = n := by
        simpa only [Int.toNat_of_nonneg (h.row_nonneg a _ (Fin.isLt _))] using h.row_size a
      exact_mod_cast he
    have hanti : Antitone (fun i : Fin r => s.eigenvalue i) := by
      intro i j hij
      rcases eq_or_lt_of_le hij with h | h
      · subst j; exact le_rfl
      · exact (s.decreasing i j h j.isLt).le
    have he := SchurProbability.schurMass_le (fun i : Fin r => (C.row a i).toNat)
      hn hsize (fun i : Fin r => s.eigenvalue i) (fun i => s.positive i i.isLt) hanti
    have hfreq : WordTypes.empirical (fun i : Fin r => (C.row a i).toNat) n =
        FiniteConcentration.rowFrequency r n (C.row a) := by
      funext i
      unfold WordTypes.empirical FiniteConcentration.rowFrequency
      congr 1
      exact_mod_cast Int.toNat_of_nonneg (h.row_nonneg a i i.isLt)
    rw [← h.probability_formula a, hfreq] at he
    exact he

/-- Actual atypical mass, now bounded from a formula rather than an inequality. -/
theorem Code.tail_le_from_tableau_gt {d r m : ℕ} (s : FixedSpectrum d r)
    (n : ℕ) (hn : 2 ≤ n) (C : Code m) (h : C.TableauGTFormula s n) :
    C.tail ≤ Concentration.tailBound (r.choose 2 + r) n :=
  C.tail_le_from_diagrams s n hn (h.toDiagramEstimate (by omega))

/-- Achievability with the entire concentration argument derived from the
actual standard-tableau and GT-character formula. -/
theorem theorem1_schur_achievability_of_tableau_gt {d r : ℕ}
    (s : FixedSpectrum d r) (hd : 2 ≤ d)
    (memory : ℕ → ℕ) (code : ∀ n, Code (memory n)) (K : ℝ) (hK : 0 ≤ K)
    (hdim : ∀ᶠ n in atTop, (memory n : ℝ) = Weyl.activeProduct d r (s.targetRow n))
    (hformulas : ∀ᶠ n in atTop, (code n).TableauGTFormula s n)
    (hf : ∀ᶠ n in atTop, ∀ i ∈ (code n).typical,
      traceDistance (((code n).forward i).toFun ((code n).state i)) (code n).target ≤
        cloningEnvelope s hd K n ((code n).row i))
    (hr : ∀ᶠ n in atTop, ∀ i ∈ (code n).typical,
      traceDistance (((code n).reverse i).toFun (code n).target) ((code n).state i) ≤
        cloningEnvelope s hd K n ((code n).row i)) :
    Tendsto (fun n => Real.logb 2 (memory n) - Weyl.qmdl d r s.eigenvalue n) atTop (𝓝 0) ∧
      Asymptotics.IsBigO atTop (fun n => (code n).error) Weyl.errorScale ∧
      Tendsto (fun n => (code n).error) atTop (𝓝 0) := by
  apply theorem1_schur_achievability_of_pointwise s hd memory code K hK hdim ?_ hf hr
  filter_upwards [hformulas, eventually_ge_atTop 1] with n hn hn1
  exact hn.toDiagramEstimate hn1

end FreeEntropy.SchurAchievability
