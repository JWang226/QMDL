/-
Copyright (c) 2026 Free Entropy formalization contributors.
See LICENSE and NOTICE in the repository root for license and attribution.
-/

import FreeEntropy.HighestWeightDominance
import FreeEntropy.TensorLieRestriction
import FreeEntropy.SchurWeylWeightExistence
import FreeEntropy.CyclicHighestRepresentation
import FreeEntropy.SchurWeylPhysical

/-! Highest vectors in actual physical tensor subspaces are obtained by
minimizing a strictly ordered energy over the finite set of word weights. -/
noncomputable section
open Matrix
open scoped BigOperators
namespace FreeEntropy.SchurWeyl
open Occupation
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
variable {d n : ℕ}

def HasTensorWeight (a : Occupation d n) (v : (Fin n → Fin d) → ℂ) : Prop :=
  ∀ k, (TensorPowers.generators d n).E k k *ᵥ v = (a.val k : ℂ) • v

def weightEnergy (a : Occupation d n) : ℝ := ∑ k, (k.val : ℝ) * (a.val k : ℝ)

theorem hasTensorWeight_of_support (a : Occupation d n) (v : (Fin n → Fin d) → ℂ)
    (hv : ∀ w, WordTypes.content w ≠ a.val → v w = 0) : HasTensorWeight a v := by
  intro k
  rw [TensorPowers.generators_diagonal]
  ext w
  simp only [Matrix.mulVec_diagonal, Pi.smul_apply, smul_eq_mul]
  by_cases hw : WordTypes.content w = a.val
  · rw [hw]
  · rw [hv w hw, mul_zero, mul_zero]

/-- A nonzero raised vector has an actual natural word weight, and its
weight energy decreases by the difference of the two matrix-unit indices. -/
theorem raising_hasTensorWeight (a : Occupation d n) (v : (Fin n → Fin d) → ℂ)
    (hv : HasTensorWeight a v) (i j : Fin d)
    (hw0 : (TensorPowers.generators d n).E i j *ᵥ v ≠ 0) :
    ∃ b : Occupation d n,
      HasTensorWeight b ((TensorPowers.generators d n).E i j *ᵥ v) ∧
      weightEnergy b = weightEnergy a + (i.val : ℝ) - (j.val : ℝ) := by
  let w := (TensorPowers.generators d n).E i j *ᵥ v
  obtain ⟨x, hx⟩ : ∃ x, w x ≠ 0 := by
    by_contra hn
    push_neg at hn
    exact hw0 (funext hn)
  let b : Occupation d n := ofWord x
  have hshift (k : Fin d) : (b.val k : ℂ) =
      (a.val k : ℂ) + (if k = i then 1 else 0) - (if k = j then 1 else 0) := by
    have h := congrFun ((TensorPowers.generators d n).raising_weight
      (fun k => (a.val k : ℂ)) v hv i j k) x
    rw [TensorPowers.generators_diagonal, Matrix.mulVec_diagonal] at h
    change (b.val k : ℂ) * w x = _ * w x at h
    exact mul_right_cancel₀ hx h
  refine ⟨b, ?_, ?_⟩
  · intro k
    rw [hshift]
    exact (TensorPowers.generators d n).raising_weight (fun k => (a.val k : ℂ)) v hv i j k
  · have hr (k : Fin d) : (b.val k : ℝ) =
        (a.val k : ℝ) + (if k = i then 1 else 0) - (if k = j then 1 else 0) := by
      have h := congrArg Complex.re (hshift k)
      simpa only [Complex.add_re, Complex.sub_re, Complex.natCast_re,
        apply_ite, Complex.one_re, Complex.zero_re] using h
    simp only [weightEnergy, hr, mul_sub, mul_add, Finset.sum_sub_distrib,
      Finset.sum_add_distrib, mul_ite, mul_one, mul_zero]
    simp

/-- Any physical tensor subspace stable under the actual Lie generators and
containing a nonzero weight vector contains a nonzero dominant highest vector.
The highest weight and raising annihilation are conclusions of the proof. -/
theorem exists_highest_of_weight (K : Submodule ℂ ((Fin n → Fin d) → ℂ))
    (hK : ∀ i j v, v ∈ K → (TensorPowers.generators d n).E i j *ᵥ v ∈ K)
    (hw : ∃ a : Occupation d n, ∃ v, v ∈ K ∧ v ≠ 0 ∧ HasTensorWeight a v) :
    ∃ a : Occupation d n, ∃ v, v ∈ K ∧ v ≠ 0 ∧ HasTensorWeight a v ∧
      Antitone a.val ∧ ∀ i j, i < j → (TensorPowers.generators d n).E i j *ᵥ v = 0 := by
  classical
  let P (a : Occupation d n) := ∃ v, v ∈ K ∧ v ≠ 0 ∧ HasTensorWeight a v
  let s := Finset.univ.filter P
  have hs : s.Nonempty := by
    obtain ⟨a, ha⟩ := hw
    exact ⟨a, by simpa [s, P] using ha⟩
  obtain ⟨a, ha, hmin⟩ := Finset.exists_min_image s weightEnergy hs
  obtain ⟨v, hvK, hv0, hva⟩ : P a := (Finset.mem_filter.mp ha).2
  have hraise (i j : Fin d) (hij : i < j) : (TensorPowers.generators d n).E i j *ᵥ v = 0 := by
    by_contra hne
    obtain ⟨b, hbw, hbE⟩ := raising_hasTensorWeight a v hva i j hne
    have hb : b ∈ s := by
      apply Finset.mem_filter.mpr
      exact ⟨Finset.mem_univ _, _, hK i j v hvK, hne, hbw⟩
    have hm := hmin b hb
    have hij' : (i.val : ℝ) < (j.val : ℝ) := by exact_mod_cast hij
    linarith
  refine ⟨a, v, hvK, hv0, hva, ?_, hraise⟩
  have hd := (TensorPowers.generators d n).highest_weight_dominant
    (fun k => (a.val k : ℝ)) v hv0 (fun k => by simpa using hva k) hraise
  intro i j hij
  have h : (a.val j : ℝ) ≤ (a.val i : ℝ) := hd hij
  exact_mod_cast h

/-- The actual invariant Hilbert subspaces are preserved by every complex
infinitesimal tensor direction, as a consequence of the proved commutant bridge. -/
theorem differential_mem (K : UnitaryDecomposition.Subspace (Fin n → Fin d))
    (hK : UnitaryDecomposition.Invariant
      (UnitaryDecomposition.euclideanRepresentation (physicalRepresentation d n)) K)
    (X : Matrix (Fin d) (Fin d) ℂ) (v : EuclideanSpace ℂ (Fin n → Fin d)) (hv : v ∈ K) :
    Matrix.toEuclideanLin (TensorPowers.differential n X) v ∈ K := by
  open UnitaryDecomposition in
  let P := embedding K * (embedding K)ᴴ
  have hcomm := (invariant_projection_commutant K hK).differential X
  have hvfix : P *ᵥ v.ofLp = v.ofLp := by
    have h := UnitaryDecomposition.embedding_projection K v
    rw [Submodule.starProjection_eq_self_iff.mpr hv] at h
    exact congrArg WithLp.ofLp h
  let w := Matrix.toEuclideanLin (TensorPowers.differential n X) v
  have hwfix : Matrix.toEuclideanLin P w = w := by
    apply WithLp.ofLp_injective 2
    change P *ᵥ (TensorPowers.differential n X *ᵥ v.ofLp) =
      TensorPowers.differential n X *ᵥ v.ofLp
    rw [Matrix.mulVec_mulVec, hcomm, ← Matrix.mulVec_mulVec, hvfix]
  have hp := UnitaryDecomposition.embedding_projection K w
  rw [hwfix] at hp
  change w ∈ K
  rw [hp]
  exact K.starProjection_apply_mem w

/-- Every nonzero actual invariant physical tensor subspace contains a
dominant highest vector. Neither its weight nor its annihilation equations
are supplied as assumptions. -/
theorem exists_physical_highest_vector (K : UnitaryDecomposition.Subspace (Fin n → Fin d))
    (hK : UnitaryDecomposition.Invariant
      (UnitaryDecomposition.euclideanRepresentation (physicalRepresentation d n)) K)
    (hK0 : K ≠ ⊥) :
    ∃ a : Occupation d n, ∃ v : EuclideanSpace ℂ (Fin n → Fin d),
      v ∈ K ∧ v ≠ 0 ∧ HasTensorWeight a v.ofLp ∧ Antitone a.val ∧
        ∀ i j, i < j → (TensorPowers.generators d n).E i j *ᵥ v.ofLp = 0 := by
  let e := (EuclideanSpace.equiv (Fin n → Fin d) ℂ).toLinearEquiv
  let L := K.comap e.symm.toLinearMap
  have hL (i j : Fin d) (v : (Fin n → Fin d) → ℂ) (hv : v ∈ L) :
      (TensorPowers.generators d n).E i j *ᵥ v ∈ L := by
    exact differential_mem K hK (Matrix.single i j 1) (e.symm v) hv
  obtain ⟨a, v, hvK, hv0, hv⟩ := exists_weight_vector K hK hK0
  have hwn : v.ofLp ≠ 0 := by
    intro h
    apply hv0
    exact WithLp.ofLp_injective 2 h
  obtain ⟨b, w, hwL, hw0, hww, hdom, hraise⟩ := exists_highest_of_weight L hL
    ⟨a, v.ofLp, hvK, hwn,
      hasTensorWeight_of_support a v.ofLp (torus_eigenvector_supported a v.ofLp hv)⟩
  refine ⟨b, e.symm w, hwL, ?_, hww, hdom, hraise⟩
  intro he
  apply hw0
  have := congrArg e he
  simpa using this

/-- In every actually constructed physical sector, a dominant highest vector
generates the entire irreducible sector under the physical unitary group. -/
theorem physical_sector_highest (i : Sector d n) :
    ∃ a : Occupation d n, ∃ v : EuclideanSpace ℂ (Fin n → Fin d),
      v ∈ i.val ∧ v ≠ 0 ∧ HasTensorWeight a v.ofLp ∧ Antitone a.val ∧
      (∀ j k, j < k → (TensorPowers.generators d n).E j k *ᵥ v.ofLp = 0) ∧
      UnitaryDecomposition.cyclicSubspace
        (UnitaryDecomposition.euclideanRepresentation (physicalRepresentation d n)) v = i.val := by
  let hK := (physicalDecomposition d n).irreducibleSubspace i.val i.property
  obtain ⟨a, v, hvK, hv0, hvw, hdom, hraise⟩ :=
    exists_physical_highest_vector i.val hK.invariant hK.ne_bot
  exact ⟨a, v, hvK, hv0, hvw, hdom, hraise,
    UnitaryDecomposition.cyclicSubspace_eq_of_irreducible _ hK hvK hv0⟩

end FreeEntropy.SchurWeyl
