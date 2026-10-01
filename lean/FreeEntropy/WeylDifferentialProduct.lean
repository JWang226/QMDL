/-
Copyright (c) 2026 Free Entropy formalization contributors.
See LICENSE and NOTICE in the repository root for license and attribution.
-/

import FreeEntropy.WeylDenominator

/-! Exact formal product rules used to convert the radial Casimir equation
into a flat Laplacian equation for the Weyl numerator. -/
noncomputable section
open scoped BigOperators
namespace FreeEntropy.WeylCharacter
open MvPolynomial
set_option backward.isDefEq.respectTransparency false
variable {d : ℕ}

theorem euler_mul (i : Fin d) (p q : MvPolynomial (Fin d) ℂ) :
    euler i (p * q) = euler i p * q + p * euler i q := by
  change X i * pderiv i (p * q) = X i * pderiv i p * q + p * (X i * pderiv i q)
  rw [pderiv_mul]
  ring

theorem euler_prod {I : Type*} [DecidableEq I] (i : Fin d) (s : Finset I)
    (f : I → MvPolynomial (Fin d) ℂ) :
    euler i (∏ a ∈ s, f a) = ∑ a ∈ s, euler i (f a) * ∏ b ∈ s.erase a, f b := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [euler, pderiv_one]
  | @insert a s ha ih =>
    rw [Finset.prod_insert ha, euler_mul, ih, Finset.sum_insert ha, Finset.erase_insert ha]
    congr 1
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro b hb
    have hba : b ≠ a := by intro h; subst b; exact ha hb
    rw [Finset.erase_insert_of_ne hba.symm, Finset.prod_insert]
    · ring
    · exact fun h => ha (Finset.mem_of_mem_erase h)

theorem laplacian_mul (p q : MvPolynomial (Fin d) ℂ) :
    laplacian (p * q) = laplacian p * q + p * laplacian q +
      2 * ∑ i : Fin d, euler i p * euler i q := by
  simp only [laplacian, LinearMap.sum_apply, LinearMap.comp_apply, euler_mul,
    map_add, Finset.sum_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- Positive roots as an actual finite set of ordered coordinate pairs. -/
def positiveRoots (d : ℕ) : Finset (Fin d × Fin d) :=
  Finset.univ.filter (fun r => r.1 < r.2)

def rootFactor (r : Fin d × Fin d) : MvPolynomial (Fin d) ℂ := X r.2 - X r.1

theorem denominator_roots (d : ℕ) : denominator d =
    ∏ r ∈ positiveRoots d, rootFactor r := by
  classical
  rw [denominator_product]
  simp only [positiveRoots, Finset.prod_filter, Fintype.prod_prod_type, rootFactor]
  apply Finset.prod_congr rfl
  intro i _
  have hs : Finset.Ioi i = Finset.univ.filter (fun j : Fin d => i < j) := by ext j; simp
  rw [hs, Finset.prod_filter]

/-- Delete one actual root factor from the denominator polynomial. -/
def denominatorWithout (r : Fin d × Fin d) : MvPolynomial (Fin d) ℂ :=
  ∏ s ∈ (positiveRoots d).erase r, rootFactor s

theorem rootFactor_mul_without (r : Fin d × Fin d) (hr : r ∈ positiveRoots d) :
    rootFactor r * denominatorWithout r = denominator d := by
  rw [denominator_roots]
  exact Finset.mul_prod_erase _ _ hr

theorem euler_rootFactor (i : Fin d) (r : Fin d × Fin d) :
    euler i (rootFactor r) =
      (if i = r.2 then X r.2 else 0) - (if i = r.1 then X r.1 else 0) := by
  classical
  change (X i : MvPolynomial (Fin d) ℂ) * pderiv i (X r.2 - X r.1) = _
  rw [map_sub, pderiv_X, pderiv_X]
  by_cases hi : i = r.2 <;> by_cases hj : i = r.1 <;>
    simp_all [Pi.single_apply]

/-- Exact cross term of the denominator product rule, with no division. -/
theorem denominator_euler_cross (p : MvPolynomial (Fin d) ℂ) :
    (∑ i : Fin d, euler i (denominator d) * euler i p) =
      ∑ r ∈ positiveRoots d, denominatorWithout r *
        (X r.2 * euler r.2 p - X r.1 * euler r.1 p) := by
  classical
  simp only [denominator_roots, euler_prod, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro r _
  simp only [euler_rootFactor, sub_mul, ite_mul, zero_mul, Finset.sum_sub_distrib]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
  change X r.2 * denominatorWithout r * euler r.2 p -
    X r.1 * denominatorWithout r * euler r.1 p = _
  ring

/-- Each coordinate occurs in exactly d-1 unordered coordinate pairs. -/
theorem sum_positiveRoots_pairs (f : Fin d → MvPolynomial (Fin d) ℂ) :
    (∑ r ∈ positiveRoots d, (f r.1 + f r.2)) = (d - 1) • ∑ i, f i := by
  classical
  have hfst : (∑ r ∈ positiveRoots d, f r.1) =
      ∑ i : Fin d, (d - 1 - i.val) • f i := by
    simp only [positiveRoots, Finset.sum_filter, Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro i _
    rw [← Finset.sum_filter]
    have hs : Finset.univ.filter (fun j : Fin d => i < j) = Finset.Ioi i := by ext j; simp
    rw [hs]
    simp [Fin.card_Ioi]
  have hsnd : (∑ r ∈ positiveRoots d, f r.2) = ∑ i : Fin d, i.val • f i := by
    simp only [positiveRoots, Finset.sum_filter, Fintype.sum_prod_type]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    rw [← Finset.sum_filter]
    have hs : Finset.univ.filter (fun j : Fin d => j < i) = Finset.Iio i := by ext j; simp
    rw [hs]
    simp [Fin.card_Iio]
  rw [Finset.sum_add_distrib, hfst, hsnd, ← Finset.sum_add_distrib, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [← add_nsmul]
  congr 1
  have := i.isLt
  omega

/-- The first-order cross term is precisely the radial Casimir numerator
plus the total degree term. This identity is entirely polynomial. -/
theorem denominator_cross_radial (p : MvPolynomial (Fin d) ℂ) :
    2 * (∑ i : Fin d, euler i (denominator d) * euler i p) =
      (d - 1 : ℕ) • (denominator d * ∑ i : Fin d, euler i p) +
      ∑ r ∈ positiveRoots d, denominatorWithout r * (X r.1 + X r.2) *
        (euler r.2 p - euler r.1 p) := by
  rw [denominator_euler_cross, Finset.mul_sum]
  have hterm (r : Fin d × Fin d) (hr : r ∈ positiveRoots d) :
      2 * (denominatorWithout r * (X r.2 * euler r.2 p - X r.1 * euler r.1 p)) =
        denominator d * (euler r.1 p + euler r.2 p) +
        denominatorWithout r * (X r.1 + X r.2) * (euler r.2 p - euler r.1 p) := by
    rw [← rootFactor_mul_without r hr]
    unfold rootFactor
    ring
  rw [Finset.sum_congr rfl hterm, Finset.sum_add_distrib, ← Finset.mul_sum,
    sum_positiveRoots_pairs (fun i => euler i p)]
  simp only [mul_smul_comm]

end FreeEntropy.WeylCharacter
