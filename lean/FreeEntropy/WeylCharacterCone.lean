/-
Copyright (c) 2026 Free Entropy formalization contributors.
See LICENSE and NOTICE in the repository root for license and attribution.
-/

import FreeEntropy.CanonicalCharacterEigen

/-! Positive-root support bounds for products of actual character polynomials.
The Vandermonde support bound follows factor by factor, without a supplied
majorization or Weyl-character formula. -/
noncomputable section
open scoped BigOperators
namespace FreeEntropy.WeylCharacter
open MvPolynomial CasimirWeights
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
variable {d : ℕ}

/-- Every nonzero coefficient lies in the integral cone below a given row. -/
def Below (a : Fin d → ℝ) (p : MvPolynomial (Fin d) ℂ) : Prop :=
  ∀ m, coeff m p ≠ 0 → ∃ c : Fin (d - 1) → ℕ,
    a - (fun i => (m i : ℝ)) = offset c

theorem offset_eq_zero_iff (c : Fin (d - 1) → ℕ) : offset c = 0 ↔ c = 0 := by
  constructor
  · intro h
    funext j
    have he := CasimirDecomposition.prefix_offset c j
    rw [h] at he
    simp only [Pi.zero_apply, Finset.sum_const_zero] at he
    exact_mod_cast he.symm
  · rintro rfl
    funext i
    simp [offset]

theorem Below.mul {a b : Fin d → ℝ} {p q : MvPolynomial (Fin d) ℂ}
    (hp : Below a p) (hq : Below b q) : Below (a + b) (p * q) := by
  classical
  intro m hm
  have hm' := support_mul p q (mem_support_iff.mpr hm)
  obtain ⟨u, hu, v, hv, rfl⟩ := Finset.mem_add.mp hm'
  obtain ⟨cu, hcu⟩ := hp u (mem_support_iff.mp hu)
  obtain ⟨cv, hcv⟩ := hq v (mem_support_iff.mp hv)
  refine ⟨cu + cv, ?_⟩
  rw [LiePBW.offset_add, ← hcu, ← hcv]
  funext i
  simp only [Pi.add_apply, Pi.sub_apply, Finsupp.add_apply, Nat.cast_add]
  ring

theorem below_one : Below (0 : Fin d → ℝ) (1 : MvPolynomial (Fin d) ℂ) := by
  intro m hm
  have he : m = 0 := by
    by_contra hn
    exact hm (by simp [coeff_one, hn, Ne.symm hn])
  subst m
  exact ⟨0, by ext i; simp [offset]⟩

theorem Below.prod {I : Type*} [DecidableEq I] (s : Finset I)
    (a : I → Fin d → ℝ) (p : I → MvPolynomial (Fin d) ℂ)
    (hp : ∀ i ∈ s, Below (a i) (p i)) : Below (∑ i ∈ s, a i) (∏ i ∈ s, p i) := by
  induction s using Finset.induction_on with
  | empty => simpa using below_one
  | @insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.prod_insert hi]
    exact (hp i (by simp)).mul (ih (fun j hj => hp j (by simp [hj])))

theorem below_rootFactor (r : Fin d × Fin d) (hr : r ∈ positiveRoots d) :
    Below (fun i => if i = r.1 then 1 else 0) (rootFactor r) := by
  classical
  have hij : r.1 < r.2 := (Finset.mem_filter.mp hr).2
  intro m hm
  by_cases hm1 : m = Finsupp.single r.1 1
  · subst m
    refine ⟨0, ?_⟩
    ext i
    simp only [Finsupp.single_apply, Pi.sub_apply, offset, Pi.zero_apply,
      Nat.cast_zero, zero_mul, Finset.sum_const_zero]
    by_cases hi : i = r.1 <;> simp [hi, eq_comm]
  · have hm2 : m = Finsupp.single r.2 1 := by
      by_contra hn
      exact hm (by simp [rootFactor, MvPolynomial.X, coeff_monomial, hm1, hn, Ne.symm hm1, Ne.symm hn])
    subst m
    obtain ⟨c, hc⟩ := LiePBW.exists_positive_root_coeff r.2 r.1 hij
    refine ⟨c, ?_⟩
    rw [hc]
    ext i
    simp only [Finsupp.single_apply, Pi.sub_apply]
    by_cases hi : i = r.1 <;> by_cases hj : i = r.2 <;> simp [hi, hj, eq_comm]

/-- The sum of the dominant endpoints of all positive roots is the staircase. -/
theorem sum_positive_root_first (k : Fin d) :
    (∑ r ∈ positiveRoots d, (if k = r.1 then (1 : ℝ) else 0)) = staircase k := by
  simp only [positiveRoots, Finset.sum_filter, Fintype.sum_prod_type]
  rw [Finset.sum_eq_single k]
  · simp only [ite_true]
    rw [← Finset.sum_filter]
    have hs : Finset.univ.filter (fun j : Fin d => k < j) = Finset.Ioi k := by ext j; simp
    rw [hs]
    simp only [Finset.sum_const, Fin.card_Ioi, nsmul_eq_mul, mul_one]
    unfold staircase
    rw [Nat.cast_sub (by omega), Nat.cast_sub (by have := k.isLt; omega)]
    norm_num
  · intro i _ hik
    simp [Ne.symm hik]
  · simp

theorem below_denominator (d : ℕ) : Below (staircase (d := d)) (denominator d) := by
  rw [denominator_roots]
  have h := Below.prod (positiveRoots d) (fun r i => if i = r.1 then (1 : ℝ) else 0)
    rootFactor (fun r hr => below_rootFactor r hr)
  convert h using 1
  funext k
  simp only [Finset.sum_apply, sum_positive_root_first]

/-- Two positive-root deficits cannot cancel. -/
theorem offsets_sum_zero (a b : Fin (d - 1) → ℕ) (h : offset a + offset b = 0) :
    a = 0 ∧ b = 0 := by
  have hab : a + b = 0 := (offset_eq_zero_iff _).mp (by rw [LiePBW.offset_add]; exact h)
  constructor <;> funext i
  · have hi := congrFun hab i; simp only [Pi.add_apply, Pi.zero_apply] at hi; change a i = 0; omega
  · have hi := congrFun hab i; simp only [Pi.add_apply, Pi.zero_apply] at hi; change b i = 0; omega

/-- The coefficient at the sum of two highest exponents is exactly the
product of their highest coefficients; no lower terms can contribute. -/
theorem coeff_mul_highest (a b : Fin d → ℕ) (p q : MvPolynomial (Fin d) ℂ)
    (hp : Below (fun i => (a i : ℝ)) p) (hq : Below (fun i => (b i : ℝ)) q) :
    coeff (exponent (a + b)) (p * q) = coeff (exponent a) p * coeff (exponent b) q := by
  classical
  rw [coeff_mul]
  have hsum : exponent a + exponent b = exponent (a + b) := by ext i; rfl
  apply Finset.sum_eq_single (exponent a, exponent b)
  · intro v hv hvne
    by_cases hp0 : coeff v.1 p = 0
    · simp [hp0]
    by_cases hq0 : coeff v.2 q = 0
    · simp [hq0]
    obtain ⟨ca, hca⟩ := hp v.1 hp0
    obtain ⟨cb, hcb⟩ := hq v.2 hq0
    have hab : offset ca + offset cb = 0 := by
      rw [← hca, ← hcb]
      have he := Finset.mem_antidiagonal.mp hv
      funext i
      have hi := congrArg (fun m : Fin d →₀ ℕ => m i) he
      simp only [Finsupp.add_apply, exponent_apply, Pi.add_apply] at hi
      have hi' : (v.1 i : ℝ) + (v.2 i : ℝ) = (a i : ℝ) + b i := by exact_mod_cast hi
      simp only [Pi.add_apply, Pi.sub_apply, Pi.zero_apply]
      linarith
    obtain ⟨hca0, hcb0⟩ := offsets_sum_zero ca cb hab
    have hleft : v.1 = exponent a := by
      rw [hca0, (offset_eq_zero_iff _).mpr rfl] at hca
      ext i
      have hi := congrFun (sub_eq_zero.mp hca) i
      exact_mod_cast hi.symm
    have hright : v.2 = exponent b := by
      rw [hcb0, (offset_eq_zero_iff _).mpr rfl] at hcb
      ext i
      have hi := congrFun (sub_eq_zero.mp hcb) i
      exact_mod_cast hi.symm
    exact (hvne (Prod.ext hleft hright)).elim
  · intro hn
    exact (hn (Finset.mem_antidiagonal.mpr hsum)).elim

end FreeEntropy.WeylCharacter
