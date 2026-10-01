/-
Copyright (c) 2026 Free Entropy formalization contributors.
See LICENSE and NOTICE in the repository root for license and attribution.
-/

import FreeEntropy.TensorInfinitesimal
import FreeEntropy.LieMatrixCasimir

/-! Actual single-site tensor actions and the Lie relations of their sum. -/
noncomputable section
open Matrix
open scoped BigOperators

namespace FreeEntropy.TensorPowers
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false
variable {H : Type*} [Fintype H] [DecidableEq H] {n : ℕ}

def family (A : Fin n → Matrix H H ℂ) : Matrix (Fin n → H) (Fin n → H) ℂ :=
  fun x y => ∏ t, A t (x t) (y t)

theorem family_mul (A B : Fin n → Matrix H H ℂ) :
    family (fun t => A t * B t) = family A * family B := by
  ext x y
  simp only [family, Matrix.mul_apply]
  rw [Fintype.prod_sum]
  simp only [Finset.prod_mul_distrib]

theorem family_adjoint (A : Fin n → Matrix H H ℂ) :
    family (fun t => (A t)ᴴ) = (family A)ᴴ := by
  ext x y
  simp [family, Matrix.conjTranspose_apply]

def site (t : Fin n) (A : Matrix H H ℂ) : Matrix (Fin n → H) (Fin n → H) ℂ :=
  family (Function.update (fun _ => 1) t A)

theorem site_apply (t : Fin n) (A : Matrix H H ℂ) (x y : Fin n → H) :
    site t A x y =
      (∏ s ∈ Finset.univ.erase t, (1 : Matrix H H ℂ) (x s) (y s)) * A (x t) (y t) := by
  unfold site family
  rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ t)]
  simp only [Function.update_self]
  congr 1
  apply Finset.prod_congr rfl
  intro s hs
  rw [Function.update_of_ne (Finset.mem_erase.mp hs).1]

theorem site_mul (t : Fin n) (A B : Matrix H H ℂ) :
    site t (A * B) = site t A * site t B := by
  rw [site, site, site, ← family_mul]
  congr 1
  funext s
  by_cases h : s = t
  · subst s; simp
  · simp [h]

theorem site_commute (s t : Fin n) (hst : s ≠ t) (A B : Matrix H H ℂ) :
    site s A * site t B = site t B * site s A := by
  simp only [site, ← family_mul]
  congr 1
  funext u
  by_cases hs : u = s
  · subst u; simp [hst]
  · by_cases ht : u = t
    · subst u; simp [hst.symm]
    · simp [hs, ht]

theorem site_sub (t : Fin n) (A B : Matrix H H ℂ) :
    site t (A - B) = site t A - site t B := by
  ext x y
  simp [site_apply, mul_sub]

theorem site_adjoint (t : Fin n) (A : Matrix H H ℂ) : site t Aᴴ = (site t A)ᴴ := by
  rw [site, site, ← family_adjoint]
  congr 1
  funext s
  by_cases h : s = t
  · subst s; simp
  · simp [h]

theorem differential_eq_sum_sites (A : Matrix H H ℂ) : differential n A = ∑ t, site t A := by
  ext x y
  simp [differential, Matrix.sum_apply, site_apply]

theorem differential_adjoint (A : Matrix H H ℂ) :
    differential n Aᴴ = (differential n A)ᴴ := by
  simp [differential_eq_sum_sites, Matrix.conjTranspose_sum, site_adjoint]

theorem site_diagonal (t : Fin n) (z : H → ℂ) :
    site t (diagonal z) = diagonal (fun x : Fin n → H => z (x t)) := by
  ext x y
  rw [site_apply]
  by_cases hxy : x = y
  · subst y; simp
  · rw [Matrix.diagonal_apply_ne _ hxy]
    obtain ⟨s, hs⟩ : ∃ s, x s ≠ y s := by
      by_contra hn
      push_neg at hn
      exact hxy (funext hn)
    by_cases hst : s = t
    · subst s; simp [Matrix.diagonal_apply_ne _ hs]
    · have hp : (∏ s ∈ Finset.univ.erase t, (1 : Matrix H H ℂ) (x s) (y s)) = 0 :=
        Finset.prod_eq_zero (by simp [hst]) (Matrix.one_apply_ne hs)
      rw [hp, zero_mul]

theorem differential_diagonal (z : H → ℂ) :
    differential n (diagonal z) = diagonal (fun x : Fin n → H => ∑ t, z (x t)) := by
  rw [differential_eq_sum_sites]
  simp only [site_diagonal]
  ext x y
  by_cases h : x = y
  · subst y; simp [Matrix.sum_apply]
  · simp [Matrix.sum_apply, Matrix.diagonal_apply_ne _ h]

/-- The infinitesimal action satisfies the full matrix Lie bracket identity. -/
theorem differential_commutator (A B : Matrix H H ℂ) :
    differential n A * differential n B - differential n B * differential n A =
      differential n (A * B - B * A) := by
  simp only [differential_eq_sum_sites, Matrix.sum_mul, Matrix.mul_sum]
  rw [Finset.sum_comm (f := fun s t => site t A * site s B), ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro s _
  rw [← Finset.sum_sub_distrib]
  rw [Finset.sum_eq_single s]
  · rw [← site_mul, ← site_mul, ← site_sub]
  · intro t _ hts
    rw [site_commute s t hts.symm, sub_self]
  · simp

@[simp] theorem differential_zero : differential n (0 : Matrix H H ℂ) = 0 := by
  ext x y
  simp [differential]

/-- Genuine `gl(d)` generators on the literal word tensor basis. -/
def generators (d n : ℕ) : LieMatrixCasimir.Generators d (Fin n → Fin d) where
  E i j := differential n (Matrix.single i j 1)
  adjoint i j := by rw [← differential_adjoint]; simp
  commutator i j k l := by
    have h := (LieMatrixCasimir.fundamental d).commutator i j k l
    simp only [LieMatrixCasimir.fundamental] at h
    rw [differential_commutator, h, differential_sub]
    change differential n (if j = k then Matrix.single i l 1 else 0) -
      differential n (if l = i then Matrix.single k j 1 else 0) = _
    split_ifs <;> simp

/-- The Cartan generators have the literal word-content weights. -/
theorem generators_diagonal (d n : ℕ) (i : Fin d) :
    (generators d n).E i i = diagonal (fun w => (WordTypes.content w i : ℂ)) := by
  change differential n (Matrix.single i i 1) = _
  rw [← Matrix.diagonal_single, differential_diagonal]
  congr 1
  funext w
  simp [Pi.single_apply, WordTypes.content, eq_comm, ← Finset.sum_boole]

end FreeEntropy.TensorPowers
