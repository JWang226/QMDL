/-
Copyright (c) 2026 Free Entropy formalization contributors.
See LICENSE and NOTICE in the repository root for license and attribution.
-/

import FreeEntropy.SchurProbabilityTableaux
import FreeEntropy.GTPartitions
import FreeEntropy.RootPartitionFunction

/-!
# Pointwise probability bound for the combinatorial Schur model

The polynomial factor is proved by counting bounded internal GT entries.
The symmetric multiplicity is the actual count of standard tableaux, and
the character is the actual sum of positive-root monomials over GT patterns.
Their product satisfies the Schur probability estimate by proved finite
word-type and matrix-free character estimates. Identifying these explicit
combinatorial quantities with a tensor-power representation decomposition
is a separate representation theorem.
-/
noncomputable section
open scoped BigOperators
namespace FreeEntropy.SchurProbability
open WordTypes SchurProbabilityTableaux GelfandTsetlin KostantWeightData
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
attribute [local instance] Classical.propDecidable
local instance {r : ℕ} {mu : Fin r → ℤ} : DecidableEq (Pattern mu) := Classical.decEq _

variable {r n : ℕ}

def integralRow (lam : Fin r → ℕ) : Fin r → ℤ := fun i => lam i

/-- Polynomial dimension bound from the actual integer GT-pattern basis. -/
theorem pattern_card_le (lam : Fin r → ℕ) (hsize : ∑ i, lam i = n) :
    Fintype.card (Pattern (integralRow lam)) ≤ (n + 1) ^ (r.choose 2) := by
  let R := {p // p ∈ Weyl.activeRoots r r}
  have htop (i : Fin r) : (0 : ℤ) ≤ integralRow lam i ∧ integralRow lam i ≤ n := by
    change (0 : ℤ) ≤ (lam i : ℤ) ∧ (lam i : ℤ) ≤ n
    constructor
    · exact_mod_cast Nat.zero_le (lam i)
    · have h := Finset.single_le_sum (f := lam) (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
      rw [hsize] at h
      exact_mod_cast h
  let raw (P : Pattern (integralRow lam)) (p : R) : ℤ :=
    P.entry ⟨p.val.2, Nat.lt_succ_of_lt (Weyl.mem_activeRoots.mp p.property).2.2⟩
      ⟨p.val.1, (Weyl.mem_activeRoots.mp p.property).2.1⟩
  have hb (P : Pattern (integralRow lam)) (p : R) : 0 ≤ raw P p ∧ raw P p ≤ n :=
    entry_bounds P htop _ _
  let code : Pattern (integralRow lam) → R → Fin (n + 1) := fun P p =>
    ⟨(raw P p).toNat, by have h := hb P p; omega⟩
  have hi : Function.Injective code := by
    intro P Q h
    apply Pattern.ext
    funext i j
    by_cases hitop : i.val = r
    · have hieq : i = Fin.last r := Fin.ext hitop
      subst i
      rw [P.top, Q.top]
    · have hir : i.val < r := by omega
      let p : R := ⟨(j.val, i.val), Weyl.mem_activeRoots.mpr ⟨j.isLt.trans hir, j.isLt, hir⟩⟩
      have he := congrArg Fin.val (congrFun h p)
      have hP := (hb P p).1
      have hQ := (hb Q p).1
      have heq : raw P p = raw Q p := by change (raw P p).toNat = (raw Q p).toNat at he; omega
      exact heq
  have hc := Fintype.card_le_of_injective code hi
  have hR : Fintype.card R = r.choose 2 := by
    rw [show Fintype.card R = (Weyl.activeRoots r r).card from Fintype.card_coe _]
    exact_mod_cast Weyl.all_root_count r
  simpa only [Fintype.card_fun, Fintype.card_fin, hR] using hc

/-- Adjacent ratios in the positive spectrum; outside the range they are zero. -/
def adjacent (x : Fin r → ℝ) (j : ℕ) : ℝ :=
  if h : j + 1 < r then x ⟨j + 1, h⟩ / x ⟨j, by omega⟩ else 0

theorem adjacent_nonneg (x : Fin r → ℝ) (hx : ∀ i, 0 < x i) (j : ℕ) :
    0 ≤ adjacent x j := by
  unfold adjacent
  split_ifs
  · exact div_nonneg (hx _).le (hx _).le
  · exact le_rfl

theorem adjacent_le_one (x : Fin r → ℝ) (hx : ∀ i, 0 < x i) (hanti : Antitone x) (j : ℕ) :
    adjacent x j ≤ 1 := by
  unfold adjacent
  split_ifs with h
  · apply (div_le_one (hx _)).mpr
    apply hanti
    change j ≤ j + 1
    omega
  · norm_num

theorem rootWeight_le_one (x : Fin r → ℝ) (hx : ∀ i, 0 < x i) (hanti : Antitone x)
    (c : (ℕ × ℕ) →₀ ℕ) : rootWeight r (adjacent x) c ≤ 1 := by
  apply Finset.prod_le_one
  · intro j _
    exact pow_nonneg (adjacent_nonneg x hx j) _
  · intro j _
    exact pow_le_one₀ (adjacent_nonneg x hx j) (adjacent_le_one x hx hanti j)

/-- The combinatorial GT character, in highest-monomial/positive-root form. -/
def gtCharacter (lam : Fin r → ℕ) (x : Fin r → ℝ) : ℝ :=
  ∑ P : Pattern (integralRow lam), monomial lam x * rootWeight r (adjacent x) (drops P)

theorem gtCharacter_le (lam : Fin r → ℕ) (x : Fin r → ℝ)
    (hx : ∀ i, 0 < x i) (hanti : Antitone x) :
    gtCharacter lam x ≤ (Fintype.card (Pattern (integralRow lam)) : ℝ) * monomial lam x := by
  calc
    _ ≤ ∑ _P : Pattern (integralRow lam), monomial lam x := by
      apply Finset.sum_le_sum
      intro P _
      exact mul_le_of_le_one_right (Finset.prod_nonneg (fun i _ => pow_nonneg (hx i).le _))
        (rootWeight_le_one x hx hanti (drops P))
    _ = _ := by simp

/-- Explicit combinatorial Schur–Weyl mass: a standard-tableau multiplicity
multiplies the GT character. This is not an assumed probability inequality. -/
def schurMass (lam : Fin r → ℕ) (n : ℕ) (x : Fin r → ℝ) : ℝ :=
  (Fintype.card (StandardTableau lam n) : ℝ) * gtCharacter lam x

/-- The pointwise Schur probability bound for the explicit combinatorial
model, derived from actual tableaux, GT patterns and finite word probabilities. -/
theorem schurMass_le (lam : Fin r → ℕ) (hn : 0 < n) (hsize : ∑ i, lam i = n)
    (x : Fin r → ℝ) (hx : ∀ i, 0 < x i) (hanti : Antitone x) :
    schurMass lam n x ≤ ((n : ℝ) + 1) ^ (r.choose 2) *
      Real.exp (-(n : ℝ) * FiniteConcentration.kl (empirical lam n) x) := by
  have hchar := gtCharacter_le lam x hx hanti
  have hcard : (Fintype.card (Pattern (integralRow lam)) : ℝ) ≤ ((n : ℝ) + 1) ^ (r.choose 2) := by
    exact_mod_cast pattern_card_le lam hsize
  have hword := tableau_monomial_le_exp_neg_kl lam hn hsize x hx
  have hm : 0 ≤ monomial lam x := Finset.prod_nonneg (fun i _ => pow_nonneg (hx i).le _)
  calc
    schurMass lam n x ≤ (Fintype.card (StandardTableau lam n) : ℝ) *
        ((Fintype.card (Pattern (integralRow lam)) : ℝ) * monomial lam x) :=
      mul_le_mul_of_nonneg_left hchar (Nat.cast_nonneg _)
    _ ≤ (Fintype.card (StandardTableau lam n) : ℝ) *
        (((n : ℝ) + 1) ^ (r.choose 2) * monomial lam x) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hcard hm) (Nat.cast_nonneg _)
    _ = ((n : ℝ) + 1) ^ (r.choose 2) *
        ((Fintype.card (StandardTableau lam n) : ℝ) * monomial lam x) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hword (by positivity)

end FreeEntropy.SchurProbability
