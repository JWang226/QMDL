/-
Copyright (c) 2026 Free Entropy formalization contributors.
See LICENSE and NOTICE in the repository root for license and attribution.
-/

import FreeEntropy.ExteriorWeights
import FreeEntropy.TensorPowers
import Mathlib.LinearAlgebra.ExteriorPower.Pairing
import Mathlib.LinearAlgebra.PiTensorProduct.Basis

/-! The genuine alternating inclusion of each exterior power into the
physical tensor power, in explicit orthonormal coordinate bases. -/
noncomputable section
open Matrix Module
open scoped BigOperators TensorProduct
namespace FreeEntropy.ExteriorRepresentation
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

variable (d k : ℕ)

def tensorBasis : Basis (Fin k → Fin d) ℂ (⨂[ℂ]^k (Fin d → ℂ)) :=
  Basis.piTensorProduct (fun _ : Fin k => Pi.basisFun ℂ (Fin d))

def alternatingEmbedding : Matrix (Fin k → Fin d) (Index d k) ℂ :=
  LinearMap.toMatrix (wedgeBasis d k) (tensorBasis d k)
    (exteriorPower.toTensorPower ℂ (Fin d → ℂ) k)

variable {d k}

def permutedEnumeration (s : Index d k) (σ : Equiv.Perm (Fin k)) : Fin k → Fin d :=
  fun i => enumerate s (σ i)

def permutationSign (σ : Equiv.Perm (Fin k)) : ℂ := ((Equiv.Perm.sign σ : ℤ) : ℂ)

def alternatingColumn (s : Index d k) : (Fin k → Fin d) → ℂ :=
  ∑ σ : Equiv.Perm (Fin k), permutationSign σ • (Pi.single (permutedEnumeration s σ) 1 : (Fin k → Fin d) → ℂ)

theorem alternatingEmbedding_column (s : Index d k) :
    (fun w => alternatingEmbedding d k w s) = alternatingColumn s := by
  funext w
  rw [alternatingEmbedding, LinearMap.toMatrix_apply]
  simp only [wedgeBasis, exteriorPower.basis_apply, exteriorPower.ιMulti_family,
    exteriorPower.toTensorPower_apply_ιMulti, Units.smul_def, map_sum, map_zsmul, Finsupp.finset_sum_apply,
    Finsupp.smul_apply, tensorBasis, Basis.piTensorProduct_repr_tprod_apply,
    Pi.basisFun_repr, Function.comp_apply, Pi.basisFun_apply]
  change (∑ σ : Equiv.Perm (Fin k), (Equiv.Perm.sign σ : ℤ) •
    ∏ i, (Pi.single (enumerate s (σ i)) 1 : Fin d → ℂ) (w i)) = _
  simp only [alternatingColumn, Finset.sum_apply, Pi.smul_apply, permutationSign,
    Units.smul_def, Int.cast_smul_eq_zsmul, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro σ _
  congr 1
  simp only [Pi.single_apply, Fintype.prod_boole]
  congr 1
  exact propext ⟨fun h => funext (fun i => h i), fun h i => congrFun h i⟩

/-- A subset and a permutation determine distinct words. -/
theorem permutedEnumeration_injective :
    Function.Injective (fun x : Index d k × Equiv.Perm (Fin k) => permutedEnumeration x.1 x.2) := by
  rintro ⟨s, σ⟩ ⟨t, τ⟩ he
  have hst : s = t := by
    apply Subtype.ext
    apply Finset.ext
    intro x
    change x ∈ s ↔ x ∈ t
    rw [← Set.powersetCard.mem_range_ofFinEmbEquiv_symm_iff_mem s x,
      ← Set.powersetCard.mem_range_ofFinEmbEquiv_symm_iff_mem t x]
    constructor
    · rintro ⟨i, rfl⟩
      refine ⟨τ (σ.symm i), ?_⟩
      have h := congrFun he (σ.symm i)
      simpa only [permutedEnumeration, Equiv.apply_symm_apply] using h.symm
    · rintro ⟨i, rfl⟩
      refine ⟨σ (τ.symm i), ?_⟩
      have h := congrFun he (τ.symm i)
      simpa only [permutedEnumeration, Equiv.apply_symm_apply] using h
  subst t
  have hp : σ = τ := by
    apply Equiv.ext
    intro i
    exact (enumerate s).injective (congrFun he i)
  subst τ
  rfl

@[simp] theorem permutedEnumeration_eq_iff (s t : Index d k) (σ τ : Equiv.Perm (Fin k)) :
    permutedEnumeration s σ = permutedEnumeration t τ ↔ s = t ∧ σ = τ := by
  constructor
  · intro h
    exact Prod.mk.inj (permutedEnumeration_injective h)
  · rintro ⟨rfl, rfl⟩
    rfl

@[simp] theorem star_permutationSign (σ : Equiv.Perm (Fin k)) :
    star (permutationSign σ) = permutationSign σ := by simp [permutationSign]

@[simp] theorem permutationSign_sq (σ : Equiv.Perm (Fin k)) :
    permutationSign σ * permutationSign σ = 1 := by
  have h := congrArg (fun z : ℤˣ => ((z : ℤ) : ℂ)) (Int.units_mul_self (Equiv.Perm.sign σ))
  simpa only [Units.val_mul, Int.cast_mul, Units.val_one, Int.cast_one] using h

/-- The unnormalized alternating basis columns have squared norm k!, and
columns for different literal subsets are orthogonal. -/
theorem alternatingColumn_inner (s t : Index d k) :
    star (alternatingColumn s) ⬝ᵥ alternatingColumn t =
      if s = t then (k.factorial : ℂ) else 0 := by
  simp only [alternatingColumn, star_sum, sum_dotProduct, dotProduct_sum, star_smul,
    star_permutationSign, ← Pi.single_star, star_one, smul_dotProduct, dotProduct_smul,
    single_dotProduct, one_mul, Pi.single_apply, permutedEnumeration_eq_iff]
  by_cases hst : s = t
  · subst t
    simp [permutationSign_sq, Fintype.card_perm]
  · simp [hst, Ne.symm hst]

theorem alternatingEmbedding_gram :
    (alternatingEmbedding d k)ᴴ * alternatingEmbedding d k = (k.factorial : ℂ) • 1 := by
  ext s t
  have h := alternatingColumn_inner s t
  have hs := alternatingEmbedding_column s
  have ht := alternatingEmbedding_column t
  change star (fun w => alternatingEmbedding d k w s) ⬝ᵥ
    (fun w => alternatingEmbedding d k w t) = _
  rw [hs, ht, h]
  simp [Matrix.one_apply]

theorem tensorMap_matrix (U : Matrix (Fin d) (Fin d) ℂ) :
    LinearMap.toMatrix (tensorBasis d k) (tensorBasis d k)
      (PiTensorProduct.map (fun _ : Fin k => Matrix.toLin' U)) = TensorPowers.matrix k U := by
  ext x y
  simp [LinearMap.toMatrix_apply, tensorBasis, Basis.piTensorProduct_apply,
    Basis.piTensorProduct_repr_tprod_apply, PiTensorProduct.map_tprod, TensorPowers.matrix,
    Matrix.toLin'_apply]

theorem exterior_toTensor_natural (U : Matrix (Fin d) (Fin d) ℂ) :
    (PiTensorProduct.map (fun _ : Fin k => Matrix.toLin' U)).comp
      (exteriorPower.toTensorPower ℂ (Fin d → ℂ) k) =
    (exteriorPower.toTensorPower ℂ (Fin d → ℂ) k).comp
      (exteriorPower.map k (Matrix.toLin' U)) := by
  apply exteriorPower.linearMap_ext
  ext v
  simp [LinearMap.compAlternatingMap_apply, exteriorPower.toTensorPower_apply_ιMulti,
    exteriorPower.map_apply_ιMulti, PiTensorProduct.map_tprod]

/-- Naturality holds for every matrix, hence in particular the actual U(d) action. -/
theorem alternatingEmbedding_intertwines (U : Matrix (Fin d) (Fin d) ℂ) :
    TensorPowers.matrix k U * alternatingEmbedding d k =
      alternatingEmbedding d k * exteriorMatrix k U := by
  rw [← tensorMap_matrix, alternatingEmbedding, exteriorMatrix,
    ← LinearMap.toMatrix_comp, ← LinearMap.toMatrix_comp, exterior_toTensor_natural]

/-- The correctly normalized alternating inclusion into the physical tensor power. -/
def wedgeEmbedding (d k : ℕ) : Matrix (Fin k → Fin d) (Index d k) ℂ :=
  (Real.sqrt (k.factorial : ℝ))⁻¹ • alternatingEmbedding d k

theorem wedgeEmbedding_isometry : (wedgeEmbedding d k)ᴴ * wedgeEmbedding d k = 1 := by
  have hp : 0 < (k.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos k
  have hs : Real.sqrt (k.factorial : ℝ) ≠ 0 := (Real.sqrt_pos.mpr hp).ne'
  have he : (Real.sqrt (k.factorial : ℝ))⁻¹ *
      ((Real.sqrt (k.factorial : ℝ))⁻¹ * (k.factorial : ℝ)) = 1 := by
    have hh := Real.sq_sqrt hp.le
    field_simp
    nlinarith
  have hgram : (alternatingEmbedding d k)ᴴ * alternatingEmbedding d k =
      (k.factorial : ℝ) • (1 : Matrix (Index d k) (Index d k) ℂ) := by
    simpa only [Complex.real_smul, Complex.ofReal_natCast] using alternatingEmbedding_gram (d := d) (k := k)
  simp only [wedgeEmbedding, Matrix.conjTranspose_smul, star_trivial, Matrix.smul_mul,
    Matrix.mul_smul, hgram, smul_smul, he, one_smul]

theorem wedgeEmbedding_intertwines (U : Matrix (Fin d) (Fin d) ℂ) :
    TensorPowers.matrix k U * wedgeEmbedding d k = wedgeEmbedding d k * exteriorMatrix k U := by
  simp only [wedgeEmbedding, Matrix.mul_smul, Matrix.smul_mul, alternatingEmbedding_intertwines]

end FreeEntropy.ExteriorRepresentation

