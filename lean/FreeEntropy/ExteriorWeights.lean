/-
Copyright (c) 2026 Free Entropy formalization contributors.
See LICENSE and NOTICE in the repository root for license and attribution.
-/

import FreeEntropy.ExteriorRepresentation
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-! Subset weights and the unique highest-weight tensor basis vector. -/
noncomputable section
open scoped BigOperators

namespace FreeEntropy.ExteriorRepresentation

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

def first {d k : ℕ} (hk : k ≤ d) : Index d k :=
  Set.powersetCard.ofFinEmbEquiv ⟨Fin.castLEEmb hk, by intro a b; rfl⟩

@[simp] theorem enumerate_first {d k : ℕ} (hk : k ≤ d) (i : Fin k) :
    enumerate (first hk) i = Fin.castLE hk i := by
  simp [first, enumerate]

theorem mem_enumerate {d k : ℕ} (s : Index d k) (i : Fin k) : enumerate s i ∈ s.val :=
  (Set.powersetCard.mem_range_ofFinEmbEquiv_symm_iff_mem s _).mp ⟨i, rfl⟩

theorem mem_first_iff {d k : ℕ} (hk : k ≤ d) (i : Fin d) :
    i ∈ (first hk).val ↔ i.val < k := by
  change i ∈ first hk ↔ _
  rw [first, Set.powersetCard.mem_ofFinEmbEquiv_iff_mem_range]
  constructor
  · rintro ⟨j, rfl⟩
    exact j.isLt
  · intro hi
    exact ⟨⟨i.val, hi⟩, Fin.ext rfl⟩

theorem sum_enumerate {d k : ℕ} {R : Type*} [AddCommMonoid R]
    (s : Index d k) (f : Fin d → R) :
    (∑ i : Fin k, f (enumerate s i)) = ∑ j ∈ s.val, f j := by
  apply Finset.sum_bij (fun i _ => enumerate s i)
  · exact fun i _ => mem_enumerate s i
  · intro i _ j _ he
    exact (enumerate s).injective he
  · intro j hj
    obtain ⟨i, hi⟩ := (Set.powersetCard.mem_range_ofFinEmbEquiv_symm_iff_mem s j).mpr hj
    exact ⟨i, Finset.mem_univ _, hi⟩
  · intro i _
    rfl

theorem enumerate_val_ge {d k : ℕ} (s : Index d k) (i : Fin k) :
    i.val ≤ (enumerate s i).val := by
  suffices ∀ n (hn : n < k), n ≤ (enumerate s ⟨n, hn⟩).val from this i.val i.isLt
  intro n
  induction n with
  | zero => intro _; exact Nat.zero_le _
  | succ n ih =>
    intro hn
    have hn' : n < k := by omega
    have hlt := (enumerate s).strictMono (show (⟨n, hn'⟩ : Fin k) < ⟨n+1, hn⟩ by exact Nat.lt_succ_self _)
    have hprev := ih hn'
    change (enumerate s ⟨n, hn'⟩).val < (enumerate s ⟨n+1, hn⟩).val at hlt
    omega

def weight {d k : ℕ} (s : Index d k) (i : Fin d) : ℕ := if i ∈ s.val then 1 else 0

def energy {d k : ℕ} (s : Index d k) : ℕ := ∑ i : Fin k, (enumerate s i).val

theorem energy_eq_weight_sum {d k : ℕ} (s : Index d k) :
    energy s = ∑ i : Fin d, i.val * weight s i := by
  rw [energy, sum_enumerate]
  simp only [weight, mul_ite, mul_one, mul_zero, ← Finset.sum_filter]
  congr 1
  ext i
  simp

theorem first_energy_le {d k : ℕ} (hk : k ≤ d) (s : Index d k) :
    energy (first hk) ≤ energy s := by
  apply Finset.sum_le_sum
  intro i _
  simpa using enumerate_val_ge s i

theorem energy_eq_first_iff {d k : ℕ} (hk : k ≤ d) (s : Index d k) :
    energy s = energy (first hk) ↔ s = first hk := by
  constructor
  · intro he
    have hcoord := (Finset.sum_eq_sum_iff_of_le (fun i (_ : i ∈ (Finset.univ : Finset (Fin k))) =>
      show (enumerate (first hk) i).val ≤ (enumerate s i).val by simpa using enumerate_val_ge s i)).mp he.symm
    apply Set.powersetCard.ofFinEmbEquiv.symm.injective
    ext i
    exact (hcoord i (Finset.mem_univ _)).symm
  · rintro rfl
    rfl

def weightPrefix {d k : ℕ} (s : Index d k) (t : ℕ) : ℕ :=
  (s.val.filter (fun i => i.val < t)).card

theorem prefix_le {d k : ℕ} (s : Index d k) (t : ℕ) : weightPrefix s t ≤ min k t := by
  apply le_min
  · exact (Finset.card_filter_le _ _).trans_eq s.property
  · have hi : (s.val.filter (fun i => i.val < t)).image Fin.val ⊆ Finset.range t := by
      intro a ha
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp ha
      exact Finset.mem_range.mpr (Finset.mem_filter.mp hi).2
    have hc := Finset.card_le_card hi
    simpa only [Finset.card_image_of_injective _ Fin.val_injective, Finset.card_range] using hc

theorem prefix_eq_enumerate {d k : ℕ} (s : Index d k) (t : ℕ) :
    weightPrefix s t = ∑ i : Fin k, if (enumerate s i).val < t then 1 else 0 := by
  simpa [weightPrefix] using
    (sum_enumerate s (fun j : Fin d => if j.val < t then (1 : ℕ) else 0)).symm

theorem prefix_eq_weight_sum {d k : ℕ} (s : Index d k) (t : ℕ) :
    weightPrefix s t = ∑ i : Fin d with i.val < t, weight s i := by
  simp only [weight, Finset.sum_boole, weightPrefix]
  congr 1
  ext i
  simp [and_comm]

theorem prefix_le_first {d k : ℕ} (hk : k ≤ d) (s : Index d k) (t : ℕ) :
    weightPrefix s t ≤ weightPrefix (first hk) t := by
  rw [prefix_eq_enumerate, prefix_eq_enumerate]
  apply Finset.sum_le_sum
  intro i _
  simp only [enumerate_first, Fin.val_castLE]
  have h := enumerate_val_ge s i
  split_ifs <;> omega

theorem sum_weight {d k : ℕ} (s : Index d k) : (∑ i : Fin d, weight s i) = k := by
  simp only [weight, Finset.sum_boole]
  have hs : Finset.univ.filter (fun i => i ∈ s.val) = s.val := by ext i; simp
  rw [hs]
  exact s.property

variable {ι : Type*} [Fintype ι] {d : ℕ} (height : ι → ℕ)

abbrev TensorIndex := ∀ a, Index d (height a)

def tensorWeight (s : TensorIndex (d := d) height) (i : Fin d) : ℕ := ∑ a, weight (s a) i

def tensorFirst (hh : ∀ a, height a ≤ d) : TensorIndex (d := d) height := fun a => first (hh a)

def tensorEnergy (s : TensorIndex (d := d) height) : ℕ := ∑ a, energy (s a)

theorem tensorEnergy_eq_weight_sum (s : TensorIndex (d := d) height) :
    tensorEnergy height s = ∑ i : Fin d, i.val * tensorWeight height s i := by
  simp only [tensorEnergy, energy_eq_weight_sum, tensorWeight]
  rw [Finset.sum_comm]
  simp only [Finset.mul_sum]

theorem tensorEnergy_highest_le (hh : ∀ a, height a ≤ d)
    (s : TensorIndex (d := d) height) :
    tensorEnergy height (tensorFirst height hh) ≤ tensorEnergy height s :=
  Finset.sum_le_sum (fun a _ => first_energy_le (hh a) (s a))

theorem tensorEnergy_eq_highest_iff (hh : ∀ a, height a ≤ d)
    (s : TensorIndex (d := d) height) :
    tensorEnergy height s = tensorEnergy height (tensorFirst height hh) ↔
      s = tensorFirst height hh := by
  constructor
  · intro he
    have hc := (Finset.sum_eq_sum_iff_of_le (fun a (_ : a ∈ (Finset.univ : Finset ι)) =>
      first_energy_le (hh a) (s a))).mp he.symm
    funext a
    exact (energy_eq_first_iff (hh a) (s a)).mp (hc a (Finset.mem_univ _)).symm
  · rintro rfl
    rfl

/-- Every tensor-product weight lies below the sum of the column-highest
weights in every prefix, without a representation-theoretic premise. -/
theorem tensor_prefix_le (s : TensorIndex (d := d) height) (t : ℕ) :
    (∑ a, weightPrefix (s a) t) ≤ ∑ a, min (height a) t :=
  Finset.sum_le_sum (fun a _ => prefix_le (s a) t)

theorem tensor_prefix_eq (s : TensorIndex (d := d) height) (t : ℕ) :
    (∑ i : Fin d with i.val < t, tensorWeight height s i) = ∑ a, weightPrefix (s a) t := by
  simp only [tensorWeight]
  rw [Finset.sum_comm]
  simp only [prefix_eq_weight_sum]

theorem tensor_prefix_le_highest (hh : ∀ a, height a ≤ d)
    (s : TensorIndex (d := d) height) (t : ℕ) :
    (∑ i : Fin d with i.val < t, tensorWeight height s i) ≤
      ∑ i : Fin d with i.val < t, tensorWeight height (tensorFirst height hh) i := by
  rw [tensor_prefix_eq, tensor_prefix_eq]
  exact Finset.sum_le_sum (fun a _ => prefix_le_first (hh a) (s a) t)

theorem tensor_sum_weight (s : TensorIndex (d := d) height) :
    (∑ i : Fin d, tensorWeight height s i) = ∑ a, height a := by
  simp only [tensorWeight]
  rw [Finset.sum_comm]
  simp only [sum_weight]

/-- The tensor-product highest weight occurs at precisely one basis vector. -/
theorem tensorWeight_eq_highest_iff (hh : ∀ a, height a ≤ d)
    (s : TensorIndex (d := d) height) :
    tensorWeight height s = tensorWeight height (tensorFirst height hh) ↔
      s = tensorFirst height hh := by
  constructor
  · intro hw
    have henergy : (∑ a, energy (s a)) = ∑ a, energy (first (hh a)) := by
      simp_rw [energy_eq_weight_sum]
      rw [Finset.sum_comm, Finset.sum_comm (f := fun a i => i.val * weight (first (hh a)) i)]
      simp_rw [← Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      exact congrArg (fun x : ℕ => i.val * x) (congrFun hw i)
    have he := (Finset.sum_eq_sum_iff_of_le (fun a (_ : a ∈ (Finset.univ : Finset ι)) =>
      first_energy_le (hh a) (s a))).mp henergy.symm
    funext a
    exact (energy_eq_first_iff (hh a) (s a)).mp (he a (Finset.mem_univ _)).symm
  · rintro rfl
    rfl

end FreeEntropy.ExteriorRepresentation
