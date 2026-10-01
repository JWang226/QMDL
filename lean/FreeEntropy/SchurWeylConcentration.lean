/-
Copyright (c) 2026 Free Entropy formalization contributors.
See LICENSE and NOTICE in the repository root for license and attribution.
-/

import FreeEntropy.SchurWeylConcentrationTail

/-! Unconditional concentration of the actual physical tensor source.
The probabilities here are traces of its constructed irreducible blocks;
the pointwise estimate, grouping, and typical tail are conclusions. -/
noncomputable section
open Matrix Filter
open scoped BigOperators Topology
namespace FreeEntropy.SchurWeyl
open Occupation
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
attribute [local instance] Classical.propDecidable
variable {d n r : ℕ}

/-- Regrouping the actual sector probabilities by their proved highest rows. -/
theorem sectorProbability_sum_grouped (x : Fin d → ℝ) (p : Occupation d n → Prop) :
    (∑ i ∈ Finset.univ.filter (fun i : Sector d n => p (sectorHighestOccupation i)),
      sectorProbability n (Matrix.diagonal (fun j => (x j : ℂ))) i) =
    ∑ lam ∈ Finset.univ.filter p, highestSectorMass lam x := by
  classical
  simp only [Finset.sum_filter]
  rw [← (Equiv.sigmaFiberEquiv (@sectorHighestOccupation d n)).sum_comp
    (fun i => if p (sectorHighestOccupation i) then
      sectorProbability n (Matrix.diagonal (fun j => (x j : ℂ))) i else 0),
    Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro lam _
  change (∑ i : SectorsAt lam, if p (sectorHighestOccupation i.val) then
    sectorProbability n (Matrix.diagonal (fun j => (x j : ℂ))) i.val else 0) = _
  simp_rw [show ∀ i : SectorsAt lam, sectorHighestOccupation i.val = lam from fun i => i.property]
  by_cases hp : p lam <;> simp [hp, highestSectorMass]

/-- The literal physical atypical mass, indexed by the actual constructed
irreducible sectors, rather than an assumed Schur probability formula. -/
def physicalAtypicalMass (s : FixedSpectrum d r) (n : ℕ) : ℝ :=
  ∑ i ∈ Finset.univ.filter (fun i : Sector d n =>
    ¬ TypicalRows.Typical s n (occupationRow (sectorHighestOccupation i))),
    sectorProbability n (Matrix.diagonal (fun j => (physicalSpectrum s j : ℂ))) i

/-- Actual mixed-state Schur concentration, with no pointwise probability,
decomposition, character, multiplicity, or dimension estimate as a premise. -/
theorem physicalAtypicalMass_le_tailBound (s : FixedSpectrum d r) (n : ℕ) (hn : 2 ≤ n) :
    physicalAtypicalMass s n ≤ Concentration.tailBound (concentrationExponent d + d) n := by
  have he := sectorProbability_sum_grouped (n := n) (physicalSpectrum s)
    (fun lam => ¬ TypicalRows.Typical s n (occupationRow lam))
  have he' : physicalAtypicalMass s n =
      ∑ lam ∈ Finset.univ.filter (fun lam : Occupation d n =>
        ¬ TypicalRows.Typical s n (occupationRow lam)), highestSectorMass lam (physicalSpectrum s) := by
    unfold physicalAtypicalMass
    simp only [Finset.sum_filter] at he ⊢
    convert he using 1 <;> apply Finset.sum_congr rfl <;> intro a _ <;> split_ifs <;> rfl
  exact he'.trans_le (physical_atypical_grouped_tail_le s n hn)

/-- The coarser proved polynomial prefactor still gives the manuscript's
required inverse-sample-size estimate eventually. -/
theorem physicalAtypicalMass_eventually_le_inv (s : FixedSpectrum d r) :
    ∀ᶠ n : ℕ in atTop, physicalAtypicalMass s n ≤ 1 / (n : ℝ) := by
  filter_upwards [Concentration.tailBound_eventually_le_inv (concentrationExponent d + d),
    eventually_ge_atTop 2] with n h hn
  exact (physicalAtypicalMass_le_tailBound s n hn).trans h

/-- Sector probabilities are constant on the physical unitary orbit. -/
theorem sectorProbability_unitary_conjugate (i : Sector d n)
    (U : Matrix.unitaryGroup (Fin d) ℂ) (ρ : Matrix (Fin d) (Fin d) ℂ) :
    sectorProbability n ((U : Matrix (Fin d) (Fin d) ℂ) * ρ *
      (U : Matrix (Fin d) (Fin d) ℂ)ᴴ) i = sectorProbability n ρ i := by
  let D := physicalDecomposition d n
  let J := D.embedding i
  let R := D.representation i
  have hL := intertwiner_adjoint R J (D.isometry i) (D.intertwines i) U
  have hR := D.intertwines i U⁻¹
  change physicalRepresentation d n U⁻¹ * J = J * R U⁻¹ at hR
  rw [Twirling.inverse_eq_conjTranspose (physicalRepresentation d n)
    (physicalRepresentation_unitary d n),
    Twirling.inverse_eq_conjTranspose R (restriction_unitary R J (D.isometry i) (D.intertwines i))] at hR
  have hcov : physicalBlock n ((U : Matrix (Fin d) (Fin d) ℂ) * ρ *
      (U : Matrix (Fin d) (Fin d) ℂ)ᴴ) i = R U * physicalBlock n ρ i * (R U)ᴴ := by
    unfold physicalBlock
    rw [TensorPowers.matrix_covariance]
    change Jᴴ * (physicalRepresentation d n U * TensorPowers.matrix n ρ *
      (physicalRepresentation d n U)ᴴ) * J =
        R U * (Jᴴ * TensorPowers.matrix n ρ * J) * (R U)ᴴ
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc Jᴴ (physicalRepresentation d n U), hL]
    simp only [Matrix.mul_assoc]
    rw [show (physicalRepresentation d n U)ᴴ * J = J * (R U)ᴴ from hR]
  unfold sectorProbability OrbitMemory.tr
  rw [hcov, Matrix.trace_mul_cycle, restriction_unitary R J (D.isometry i) (D.intertwines i) U, Matrix.one_mul]

/-- The same tail controls every member of the actual mixed-state orbit. -/
theorem physical_orbit_atypical_tail_le (s : FixedSpectrum d r) (n : ℕ) (hn : 2 ≤ n)
    (U : Matrix.unitaryGroup (Fin d) ℂ) :
    (∑ i ∈ Finset.univ.filter (fun i : Sector d n =>
      ¬ TypicalRows.Typical s n (occupationRow (sectorHighestOccupation i))),
      sectorProbability n ((U : Matrix (Fin d) (Fin d) ℂ) *
        Matrix.diagonal (fun j => (physicalSpectrum s j : ℂ)) *
          (U : Matrix (Fin d) (Fin d) ℂ)ᴴ) i) ≤
      Concentration.tailBound (concentrationExponent d + d) n := by
  simp_rw [sectorProbability_unitary_conjugate]
  exact physicalAtypicalMass_le_tailBound s n hn

end FreeEntropy.SchurWeyl
