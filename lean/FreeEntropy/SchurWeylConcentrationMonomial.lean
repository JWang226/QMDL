/-
Copyright (c) 2026 Free Entropy formalization contributors.
See LICENSE and NOTICE in the repository root for license and attribution.
-/

import FreeEntropy.SchurWeylConcentrationGrouping

/-! Highest-monomial domination follows from the proved positive root cone.
The nonnegative version includes physical spectra with zero eigenvalues. -/
noncomputable section
open Matrix Filter
open scoped BigOperators Topology
namespace FreeEntropy.SchurWeyl
open Occupation WordTypes CasimirWeights
set_option backward.isDefEq.respectTransparency false
variable {d n : ℕ}

theorem monomial_le_of_root_cone_pos (lam mu : Fin d → ℕ) (c : Fin (d - 1) → ℕ)
    (hcone : (fun j => (lam j : ℝ)) - (fun j => (mu j : ℝ)) = offset c)
    (x : Fin d → ℝ) (hx : ∀ j, 0 < x j) (hanti : Antitone x) :
    monomial mu x ≤ monomial lam x := by
  have hlog (a : Fin d → ℕ) : Real.log (monomial a x) =
      ∑ j, (a j : ℝ) * Real.log (x j) := by
    rw [monomial, Real.log_prod (fun j _ => pow_ne_zero _ (hx j).ne')]
    simp only [Real.log_pow]
  have hnonneg : 0 ≤ dot (fun j => Real.log (x j)) (offset c) := by
    apply (offset_dot_bounds c (fun j => Real.log (x j)) ?_).1
    intro j
    exact Real.log_le_log (hx _) (hanti (show left j ≤ right j by
      change j.val ≤ j.val + 1; omega))
  have hdiff : Real.log (monomial lam x) - Real.log (monomial mu x) =
      dot (fun j => Real.log (x j)) (offset c) := by
    rw [hlog, hlog, ← hcone]
    simp only [dot, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]
    congr 1 <;> apply Finset.sum_congr rfl <;> intro j _ <;> ring
  apply (Real.log_le_log_iff (Finset.prod_pos (fun j _ => pow_pos (hx j) _))
    (Finset.prod_pos (fun j _ => pow_pos (hx j) _))).mp
  change Real.log (monomial mu x) ≤ Real.log (monomial lam x)
  linarith

/-- Continuity extends highest-monomial domination to rank-deficient spectra. -/
theorem monomial_le_of_root_cone (lam mu : Fin d → ℕ) (c : Fin (d - 1) → ℕ)
    (hcone : (fun j => (lam j : ℝ)) - (fun j => (mu j : ℝ)) = offset c)
    (x : Fin d → ℝ) (hx : ∀ j, 0 ≤ x j) (hanti : Antitone x) :
    monomial mu x ≤ monomial lam x := by
  have hcont (a : Fin d → ℕ) : Continuous (fun ε : ℝ => monomial a (fun j => x j + ε)) := by
    unfold monomial
    fun_prop
  have hm (ε : ℝ) (hε : 0 < ε) :
      monomial mu (fun j => x j + ε) ≤ monomial lam (fun j => x j + ε) :=
    monomial_le_of_root_cone_pos lam mu c hcone (fun j => x j + ε)
      (fun j => lt_of_le_of_lt (hx j) (lt_add_of_pos_right _ hε))
      (fun i j hij => by simpa only [add_comm] using add_le_add_right (hanti hij) ε)
  have ht (a : Fin d → ℕ) : Tendsto (fun ε : ℝ => monomial a (fun j => x j + ε))
      (𝓝[>] 0) (𝓝 (monomial a x)) := by
    simpa only [add_zero] using ((hcont a).continuousAt (x := 0)).tendsto.mono_left (nhdsWithin_le_nhds (s := Set.Ioi 0))
  exact le_of_tendsto_of_tendsto (ht mu) (ht lam)
    (eventually_mem_nhdsWithin.mono fun ε hε => hm ε hε)

theorem sector_monomial_le_highest (i : Sector d n) (a : SectorSpace d n i)
    (x : Fin d → ℝ) (hx : ∀ j, 0 ≤ x j) (hanti : Antitone x) :
    monomial (sectorWeight i a).val x ≤ monomial (sectorHighestOccupation i).val x :=
  monomial_le_of_root_cone _ _ (sectorWeightCoefficients i a)
    (sectorWeightCoefficients_spec i a) x hx hanti

/-- The probability of each actual irreducible block is its exact character
sum in the constructed occupation basis. -/
theorem sectorProbability_diagonal (i : Sector d n) (x : Fin d → ℝ) :
    sectorProbability n (Matrix.diagonal (fun j => (x j : ℂ))) i =
      ∑ a : SectorSpace d n i, monomial (sectorWeight i a).val x := by
  have h := congrArg Matrix.trace (physicalBlock_weight_diagonal i (fun j => (x j : ℂ)))
  rw [Matrix.trace_mul_cycle, sectorWeightUnitary_coisometry, Matrix.one_mul,
    Matrix.trace_diagonal] at h
  have hr := congrArg Complex.re h
  simpa [sectorProbability, OrbitMemory.tr, character, monomial, ← Complex.ofReal_pow,
    ← Complex.ofReal_prod] using hr

/-- An actual physical block is bounded by its actual dimension times the
highest monomial; zero eigenvalues are allowed. -/
theorem sectorProbability_le_highest (i : Sector d n) (x : Fin d → ℝ)
    (hx : ∀ j, 0 ≤ x j) (hanti : Antitone x) :
    sectorProbability n (Matrix.diagonal (fun j => (x j : ℂ))) i ≤
      (Fintype.card (SectorSpace d n i) : ℝ) * monomial (sectorHighestOccupation i).val x := by
  rw [sectorProbability_diagonal]
  calc
    _ ≤ ∑ _a : SectorSpace d n i, monomial (sectorHighestOccupation i).val x :=
      Finset.sum_le_sum fun a _ => sector_monomial_le_highest i a x hx hanti
    _ = _ := by simp

end FreeEntropy.SchurWeyl
