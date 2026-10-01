/-
Copyright (c) 2026 Free Entropy formalization contributors.
See LICENSE and NOTICE in the repository root for license and attribution.
-/

import FreeEntropy.RaisingKernel
import FreeEntropy.SignedCartan
import FreeEntropy.CoordinateWeightSpace

/-! Genuine monotonicity of all weight multiplicities under Cartan addition.
The highest auxiliary slice is injective: its kernel is raising-invariant
and cannot contain the source highest line. -/
noncomputable section
open Matrix
open scoped BigOperators Kronecker
namespace FreeEntropy.CartanLieCloning
open LieMatrixCasimir CartanChannel
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
variable {d : ℕ} {A B C : Type*} [Fintype A] [DecidableEq A]
  [Fintype B] [DecidableEq B] [Fintype C] [DecidableEq C]
  [Nonempty A] [Nonempty B] [Nonempty C]

theorem tensor_basisEmbedding_raise (M : CyclicWeightModel d A) (N : CyclicWeightModel d B)
    (i j : Fin d) (hij : i < j) :
    (M.generators.tensor N.generators).E i j * basisEmbedding N.highestBasis =
      basisEmbedding N.highestBasis * M.generators.E i j := by
  ext ⟨a,b⟩ c
  simp only [Generators.tensor, Matrix.mul_apply, Matrix.add_apply, Matrix.kronecker_apply,
    basisEmbedding, Fintype.sum_prod_type, Matrix.one_apply]
  simp only [mul_ite, mul_zero, mul_one, ite_mul, zero_mul, one_mul,
    Finset.sum_ite_eq', Finset.mem_univ, if_true]
  simp [N.highest_basis_raise N.highestBasis N.highestBasis_weight i j hij, add_mul,
    Finset.sum_add_distrib, mul_ite, ite_mul, and_comm]

theorem cartanSlice_raise (M : CyclicWeightModel d A) (N : CyclicWeightModel d B)
    (S : CyclicWeightModel d C) (J : Matrix (A × B) C ℂ)
    (hJ : ∀ i j, (M.generators.tensor N.generators).E i j * J = J * S.generators.E i j)
    (i j : Fin d) (hij : i < j) :
    S.generators.E i j * sliceKraus J N.highestBasis =
      sliceKraus J N.highestBasis * M.generators.E i j := by
  have h := congrArg Matrix.conjTranspose (hJ j i)
  simp only [Matrix.conjTranspose_mul, Generators.adjoint] at h
  rw [sliceKraus_eq_compression, ← Matrix.mul_assoc, ← h, Matrix.mul_assoc,
    tensor_basisEmbedding_raise M N i j hij, ← Matrix.mul_assoc]

theorem cartan_top_entry_ne_zero (M : CyclicWeightModel d A) (N : CyclicWeightModel d B)
    (S : CyclicWeightModel d C) (J : Matrix (A × B) C ℂ) (hiso : Jᴴ * J = 1)
    (hJ : ∀ i j, (M.generators.tensor N.generators).E i j * J = J * S.generators.E i j)
    (hrow : S.row = M.row + N.row) :
    J (M.highestBasis, N.highestBasis) S.highestBasis ≠ 0 := by
  obtain ⟨ab, hab⟩ := isometry_column_nonzero J hiso S.highestBasis
  by_cases he : ab = (M.highestBasis, N.highestBasis)
  · simpa only [he] using hab
  · exact (hab (tensor_top_column_support M N S J hJ hrow ab he)).elim

/-- The actual highest auxiliary Kraus slice is injective. -/
theorem cartanSlice_injective (M : CyclicWeightModel d A) (N : CyclicWeightModel d B)
    (S : CyclicWeightModel d C) (J : Matrix (A × B) C ℂ) (hiso : Jᴴ * J = 1)
    (hJ : ∀ i j, (M.generators.tensor N.generators).E i j * J = J * S.generators.E i j)
    (hrow : S.row = M.row + N.row) :
    Function.Injective (Matrix.toLin' (sliceKraus J N.highestBasis)) := by
  apply LinearMap.ker_eq_bot.mp
  apply M.eq_bot_of_raising_invariant
  · intro i j hij v hv
    change sliceKraus J N.highestBasis *ᵥ (M.generators.E i j *ᵥ v) = 0
    rw [Matrix.mulVec_mulVec, ← cartanSlice_raise M N S J hJ i j hij,
      ← Matrix.mulVec_mulVec]
    change S.generators.E i j *ᵥ ((Matrix.toLin' (sliceKraus J N.highestBasis)) v) = 0
    rw [LinearMap.mem_ker.mp hv, Matrix.mulVec_zero]
  · intro hh
    have he_raise : ∀ i j, i < j → M.generators.E i j *ᵥ Pi.single M.highestBasis (1 : ℂ) = 0 := by
      intro i j hij
      funext a
      simpa using M.highest_basis_raise M.highestBasis M.highestBasis_weight i j hij a
    obtain ⟨c, hc⟩ := M.highest_line_unique (Pi.single M.highestBasis 1) he_raise
    have hs := (LinearMap.ker (Matrix.toLin' (sliceKraus J N.highestBasis))).smul_mem c hh
    rw [← hc] at hs
    have hz := congrFun (LinearMap.mem_ker.mp hs) S.highestBasis
    have hne := cartan_top_entry_ne_zero M N S J hiso hJ hrow
    exact hne (by simpa [Matrix.toLin'_apply, sliceKraus] using hz)

/-- The nonzero entries of the slice have the exact shifted weight. -/
theorem cartanSlice_weight (M : CyclicWeightModel d A) (N : CyclicWeightModel d B)
    (S : CyclicWeightModel d C) (J : Matrix (A × B) C ℂ)
    (hJ : ∀ i j, (M.generators.tensor N.generators).E i j * J = J * S.generators.E i j)
    (c : C) (a : A) (hne : sliceKraus J N.highestBasis c a ≠ 0) :
    S.weight c = M.weight a + N.row := by
  have he := tensor_intertwiner_weight M N S J hJ (a, N.highestBasis) c
    (by simpa only [sliceKraus, ne_eq, star_eq_zero] using hne)
  simpa only [N.highestBasis_weight] using he.symm

private theorem real_weight_eq_iff (a b : Fin d → ℝ) :
    (fun k => (a k : ℂ)) = (fun k => (b k : ℂ)) ↔ a = b := by
  constructor
  · intro h
    funext k
    exact Complex.ofReal_injective (congrFun h k)
  · rintro rfl
    rfl

/-- Every source weight multiplicity is at most the corresponding shifted
target weight multiplicity. All Cartan existence and injectivity inputs
are discharged by the constructed isometry and the raising argument. -/
theorem weight_multiplicity_add_le (M : CyclicWeightModel d A) (N : CyclicWeightModel d B)
    (S : CyclicWeightModel d C) (hrow : S.row = M.row + N.row) (wt : Fin d → ℝ) :
    Fintype.card {a : A // M.weight a = wt} ≤
      Fintype.card {c : C // S.weight c = wt + N.row} := by
  classical
  let J := canonicalCartanIsometry M N S hrow
  have hJ := canonicalCartanIsometry_spec M N S hrow
  let X := LiePBW.coordinateWeightSpace (fun a k => (M.weight a k : ℂ)) (fun k => (wt k : ℂ))
  let Y := LiePBW.coordinateWeightSpace (fun c k => (S.weight c k : ℂ)) (fun k => ((wt + N.row) k : ℂ))
  let F := sliceKraus J N.highestBasis
  let f : X →ₗ[ℂ] Y :=
    { toFun := fun x => ⟨F *ᵥ x.val, by
        intro c hc
        have hc' : S.weight c ≠ wt + N.row := mt (real_weight_eq_iff _ _).mpr hc
        change ∑ a, F c a * x.val a = 0
        apply Finset.sum_eq_zero
        intro a _
        by_cases ha : M.weight a = wt
        · have hz : F c a = 0 := by
            by_contra hn
            have he := cartanSlice_weight M N S J hJ.2.1 c a hn
            rw [ha] at he
            exact hc' he
          rw [hz, zero_mul]
        · have hz := x.property a (mt (real_weight_eq_iff _ _).mp ha)
          rw [hz, mul_zero]⟩
      map_add' := by intros; apply Subtype.ext; exact Matrix.mulVec_add _ _ _
      map_smul' := by intros; apply Subtype.ext; exact Matrix.mulVec_smul _ _ _ }
  have hf : Function.Injective f := by
    intro x y h
    apply Subtype.ext
    exact cartanSlice_injective M N S J hJ.1 hJ.2.1 hrow (congrArg Subtype.val h)
  have hx : Module.finrank ℂ X = Fintype.card {a : A // M.weight a = wt} := by
    rw [LiePBW.coordinateWeightSpace_finrank]
    exact Fintype.card_congr (Equiv.subtypeEquivRight (fun a => real_weight_eq_iff _ _))
  have hy : Module.finrank ℂ Y = Fintype.card {c : C // S.weight c = wt + N.row} := by
    rw [LiePBW.coordinateWeightSpace_finrank]
    exact Fintype.card_congr (Equiv.subtypeEquivRight (fun c => real_weight_eq_iff _ _))
  exact hx ▸ hy ▸ LinearMap.finrank_le_finrank_of_injective hf

end FreeEntropy.CartanLieCloning
