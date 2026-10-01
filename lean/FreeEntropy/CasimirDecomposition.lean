/-
Copyright (c) 2026 Free Entropy formalization contributors.
See LICENSE and NOTICE in the repository root for license and attribution.
-/

import FreeEntropy.LieMatrixCasimir
import FreeEntropy.CasimirCentral
import FreeEntropy.SectorChannels

/-!
# Local Casimir gaps from actual highest-weight decompositions

Complete families of intertwining isometries identify the actual Casimir
with a sum of its scalar constituent actions. Joint-weight projectors give
the corresponding local decomposition. The operator gap then follows from
the proved Casimir polynomial arithmetic, rather than being assumed.
-/

noncomputable section
open scoped BigOperators Matrix ComplexOrder MatrixOrder
open Matrix

namespace FreeEntropy.CasimirDecomposition
open CasimirWeights
open LieMatrixCasimir WeightSectors

set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false

variable {ι H : Type*} [Fintype ι] [DecidableEq ι] [Fintype H] [DecidableEq H]
variable {B : ι → Type*} [∀ i, Fintype (B i)] [∀ i, DecidableEq (B i)]

/-- Prefix sums recover the coefficients of actual type-A simple roots. -/
theorem prefix_offset {d : ℕ} (c : Fin (d - 1) → ℕ) (j : Fin (d - 1)) :
    (∑ i : Fin d with i.val ≤ j.val, offset c i) = (c j : ℝ) := by
  let s : Finset (Fin d) := Finset.univ.filter (fun i => i.val ≤ j.val)
  have hroot (k : Fin (d - 1)) : (∑ i ∈ s, simpleRoot k i) = if k = j then 1 else 0 := by
    simp only [simpleRoot, Finset.sum_sub_distrib]
    simp only [Finset.sum_ite_eq', Finset.mem_filter, Finset.mem_univ, true_and,
      s, left, right]
    by_cases hk : k = j
    · subst k
      simp
    · have hne : k.val ≠ j.val := fun he => hk (Fin.ext he)
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · simp [hk, Nat.le_of_lt hlt, show k.val + 1 ≤ j.val by omega]
      · simp [hk, show ¬k.val ≤ j.val by omega, show ¬k.val + 1 ≤ j.val by omega]
  change (∑ i ∈ s, ∑ k, (c k : ℝ) * simpleRoot k i) = _
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum, hroot]
  simp

/-- A constituent reaching a lower weight has no more of any simple-root
deficit than that weight. This is derived from the two actual root-cone equations. -/
theorem coefficient_le_of_weight_cones {d : ℕ} (nu chi lam : Fin d → ℝ)
    (c b delta : Fin (d - 1) → ℕ)
    (hc : nu - chi = offset c) (hb : chi - lam = offset b)
    (hdelta : nu - lam = offset delta) : ∀ j, c j ≤ delta j := by
  have he : offset c + offset b = offset delta := by
    rw [← hc, ← hb, ← hdelta]
    abel
  intro j
  have hp := congrArg (fun v : Fin d → ℝ => ∑ i : Fin d with i.val ≤ j.val, v i) he
  simp only [Pi.add_apply, Finset.sum_add_distrib, prefix_offset] at hp
  have hb0 : (0 : ℝ) ≤ b j := Nat.cast_nonneg _
  exact_mod_cast (show (c j : ℝ) ≤ delta j by linarith)

/-- A complete family of constituent embeddings converts scalar Casimir
actions into the actual operator decomposition. -/
theorem operator_eq_sum_of_eigen_embeddings (C : Matrix H H ℂ)
    (V : ∀ i, Matrix H (B i) ℂ) (c : ι → ℝ)
    (hresolve : ∑ i, V i * (V i)ᴴ = 1)
    (heigen : ∀ i, C * V i = c i • V i) :
    C = ∑ i, c i • (V i * (V i)ᴴ) := by
  calc
    C = C * (∑ i, V i * (V i)ᴴ) := by rw [hresolve, Matrix.mul_one]
    _ = ∑ i, (C * V i) * (V i)ᴴ := by simp only [Matrix.mul_sum, Matrix.mul_assoc]
    _ = _ := by simp only [heigen, Matrix.smul_mul]

theorem sector_eq_sum_of_intertwining (S : Matrix H H ℂ)
    (V : ∀ i, Matrix H (B i) ℂ) (P : ∀ i, Matrix (B i) (B i) ℂ)
    (hresolve : ∑ i, V i * (V i)ᴴ = 1)
    (hsector : ∀ i, S * V i = V i * P i) :
    S = ∑ i, V i * P i * (V i)ᴴ := by
  calc
    S = S * (∑ i, V i * (V i)ᴴ) := by rw [hresolve, Matrix.mul_one]
    _ = ∑ i, (S * V i) * (V i)ᴴ := by simp only [Matrix.mul_sum, Matrix.mul_assoc]
    _ = _ := by simp only [hsector]

/-- The local gap follows from scalar eigenvalues on actual constituent
embeddings. Only constituents meeting the chosen sector need a large gap. -/
theorem local_gap_of_eigen_embeddings (C S : Matrix H H ℂ)
    (V : ∀ i, Matrix H (B i) ℂ) (P : ∀ i, Matrix (B i) (B i) ℂ)
    (c : ι → ℝ) (top : ι) (gap : ℝ) (hgap : 0 ≤ gap)
    (hresolve : ∑ i, V i * (V i)ᴴ = 1)
    (heigen : ∀ i, C * V i = c i • V i)
    (hsector : ∀ i, S * V i = V i * P i)
    (hP : ∀ i, IsStarProjection (P i))
    (hmax : ∀ i, c i ≤ c top)
    (hlocal : ∀ i, i ≠ top → P i ≠ 0 → gap ≤ c top - c i) :
    gap • (S - V top * P top * (V top)ᴴ) ≤ c top • (1 : Matrix H H ℂ) - C := by
  let a (i : ι) : ℝ := if i = top then 0 else gap
  have hblock (i : ι) :
      ((c top - c i) • (V i * (V i)ᴴ) - a i • (V i * P i * (V i)ᴴ)).PosSemidef := by
    have hinner : ((c top - c i) • (1 : Matrix (B i) (B i) ℂ) - a i • P i).PosSemidef := by
      by_cases hit : i = top
      · subst i
        simpa [a] using (Matrix.PosSemidef.zero : (0 : Matrix (B top) (B top) ℂ).PosSemidef)
      · by_cases hzero : P i = 0
        · simpa [a, hit, hzero] using Matrix.PosSemidef.one.smul (sub_nonneg.mpr (hmax i))
        · have hdiff : 0 ≤ c top - c i - gap := sub_nonneg.mpr (hlocal i hit hzero)
          have hp := (Matrix.PosSemidef.one.smul hdiff).add
            ((hP i).one_sub_nonneg.posSemidef.smul hgap)
          convert hp using 1
          simp only [a, if_neg hit]
          module
    have h := hinner.mul_mul_conjTranspose_same (V i)
    simpa only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul,
      Matrix.mul_one] using h
  have hsum := Matrix.posSemidef_sum Finset.univ (fun i _ => hblock i)
  have ha : (∑ i, a i • (V i * P i * (V i)ᴴ)) =
      gap • S - gap • (V top * P top * (V top)ᴴ) := by
    have hi (i : ι) : a i • (V i * P i * (V i)ᴴ) =
        gap • (V i * P i * (V i)ᴴ) -
          (if i = top then gap • (V i * P i * (V i)ᴴ) else 0) := by
      by_cases hit : i = top <;> simp [a, hit]
    simp_rw [hi]
    rw [Finset.sum_sub_distrib, Finset.sum_ite_eq', if_pos (Finset.mem_univ top),
      ← Finset.smul_sum, ← sector_eq_sum_of_intertwining S V P hresolve hsector]
  have hc : (∑ i, (c top - c i) • (V i * (V i)ᴴ)) = c top • (1 : Matrix H H ℂ) - C := by
    simp_rw [sub_smul]
    rw [Finset.sum_sub_distrib, ← Finset.smul_sum, hresolve,
      ← operator_eq_sum_of_eigen_embeddings C V c hresolve heigen]
  apply Matrix.le_iff.mpr
  simpa only [Finset.sum_sub_distrib, hc, ha, smul_sub] using hsum

/-- Highest-weight root offsets and dominance supply every scalar spectral
inequality in the local operator gap. Completeness/intertwining are actual
matrix decomposition data; no Casimir PSD bound or eigenvalue gap is input. -/
theorem local_gap_of_highest_weights {d : ℕ} (C S : Matrix H H ℂ)
    (V : ∀ i, Matrix H (B i) ℂ) (P : ∀ i, Matrix (B i) (B i) ℂ)
    (chi : ι → Fin d → ℝ) (nu : Fin d → ℝ)
    (coeff : ι → Fin (d - 1) → ℕ) (top : ι) (g : ℝ) (hg : 0 ≤ g)
    (hresolve : ∑ i, V i * (V i)ᴴ = 1)
    (heigen : ∀ i, C * V i = casimir (chi i) • V i)
    (hsector : ∀ i, S * V i = V i * P i)
    (hP : ∀ i, IsStarProjection (P i))
    (htop : chi top = nu)
    (hdiff : ∀ i, nu - chi i = offset (coeff i))
    (hnu : ∀ j, nu (right j) ≤ nu (left j))
    (hchi : ∀ i j, chi i (right j) ≤ chi i (left j))
    (hnonzero : ∀ i, i ≠ top → P i ≠ 0 → ∃ j, coeff i j ≠ 0)
    (hgap : ∀ i, i ≠ top → P i ≠ 0 → ∀ j, coeff i j ≠ 0 →
      g ≤ nu (left j) - nu (right j)) :
    (g + 2) • (S - V top * P top * (V top)ᴴ) ≤
      casimir nu • (1 : Matrix H H ℂ) - C := by
  have hc : casimir (chi top) = casimir nu := congrArg casimir htop
  rw [← hc]
  apply local_gap_of_eigen_embeddings C S V P (fun i => casimir (chi i)) top (g + 2)
    (by linarith) hresolve heigen hsector hP
  · intro i
    have h := casimir_gap_times_depth nu (chi i) (coeff i) 0 (hdiff i)
      (fun j _ => sub_nonneg.mpr (hnu j)) (hchi i)
    rw [hc]
    have hn : 0 ≤ (depth (coeff i) : ℝ) := Nat.cast_nonneg _
    linarith
  · intro i hi hPi
    rw [hc]
    exact casimir_gap nu (chi i) (coeff i) g hg (hnonzero i hi hPi) (hdiff i)
      (hgap i hi hPi) (hchi i)

/-- Concrete matrix representation data discharge the Casimir eigenvalue,
weight-projector intertwining, and local spectral-gap hypotheses. The input
is a complete decomposition into cyclic highest-weight representations,
with their actual basis weights lying in their highest-weight root cones.
Only adjacent gaps met by the chosen weight deficit are needed. -/
theorem local_gap_of_cyclic_weight_decomposition {d : ℕ}
    (R : Generators d H) (Ri : ∀ i, Generators d (B i))
    (V : ∀ i, Matrix H (B i) ℂ)
    (w : H → Fin d → ℝ) (wi : ∀ i, B i → Fin d → ℝ)
    (highest : ∀ i, Matrix (B i) Unit ℂ)
    (chi : ι → Fin d → ℝ) (nu lam : Fin d → ℝ)
    (coeff : ι → Fin (d - 1) → ℕ)
    (remaining : ∀ i, B i → Fin (d - 1) → ℕ)
    (delta : Fin (d - 1) → ℕ) (top : ι) (g : ℝ) (hg : 0 ≤ g)
    (hresolve : ∑ i, V i * (V i)ᴴ = 1)
    (hintertwine : ∀ i a b, R.E a b * V i = V i * (Ri i).E a b)
    (hdiag : ∀ j, R.E j j = weightDiagonal w j)
    (hdiagi : ∀ i j, (Ri i).E j j = weightDiagonal (wi i) j)
    (hhighest_weight : ∀ i j, (Ri i).E j j * highest i = chi i j • highest i)
    (hhighest_raise : ∀ i a b, a < b → (Ri i).E a b * highest i = 0)
    (hcyclic : ∀ i, (Ri i).cyclicSpan (highest i) = ⊤)
    (htop : chi top = nu)
    (hunique : ∀ i, chi i = nu → i = top)
    (hdiff : ∀ i, nu - chi i = offset (coeff i))
    (hweights : ∀ i k, chi i - wi i k = offset (remaining i k))
    (hdelta : nu - lam = offset delta)
    (hnu : ∀ j, nu (right j) ≤ nu (left j))
    (hchi : ∀ i j, chi i (right j) ≤ chi i (left j))
    (hgap : ∀ j, delta j ≠ 0 → g ≤ nu (left j) - nu (right j)) :
    (g + 2) • (weightProjector w lam -
      V top * weightProjector (wi top) lam * (V top)ᴴ) ≤
      casimir nu • (1 : Matrix H H ℂ) - R.casimir := by
  classical
  apply local_gap_of_highest_weights R.casimir (weightProjector w lam)
    V (fun i => weightProjector (wi i) lam) chi nu coeff top g hg hresolve
  · intro i
    rw [R.casimir_intertwines (Ri i) (V i) (hintertwine i),
      (Ri i).casimir_eq_scalar_of_cyclic (highest i) (chi i)
        (hhighest_weight i) (hhighest_raise i) (hcyclic i),
      Matrix.mul_smul, Matrix.mul_one]
  · intro i
    apply weightProjector_intertwines
    intro j
    rw [← hdiag j, ← hdiagi i j]
    exact hintertwine i j j
  · intro i
    exact weightProjector_isStarProjection (wi i) lam
  · exact htop
  · exact hdiff
  · exact hnu
  · exact hchi
  · intro i hi _
    by_contra hn
    push_neg at hn
    apply hi
    apply hunique i
    have hz : offset (coeff i) = 0 := by
      ext j
      simp [offset, hn]
    have he := (hdiff i).trans hz
    exact (sub_eq_zero.mp he).symm
  · intro i _ hP j hj
    obtain ⟨k, hk⟩ := (weightProjector_ne_zero_iff (wi i) lam).mp hP
    have hb := hweights i k
    rw [hk] at hb
    have hle := coefficient_le_of_weight_cones nu (chi i) lam (coeff i)
      (remaining i k) delta (hdiff i) hb hdelta j
    exact hgap j (by omega)

end FreeEntropy.CasimirDecomposition
