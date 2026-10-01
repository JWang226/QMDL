/-
Copyright (c) 2026 Free Entropy formalization contributors.
See LICENSE and NOTICE in the repository root for license and attribution.
-/

import FreeEntropy.ExteriorCanonicalHighest
import FreeEntropy.LieHighestUnitary
import FreeEntropy.TensorLieIntertwiners
import FreeEntropy.TensorLieCyclicityPhysical

/-! Actual classification of physical tensor sectors by the constructed
canonical exterior highest-weight representations. -/
noncomputable section
open Matrix
namespace FreeEntropy
open ExteriorRepresentation
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
variable {d n : ℕ} {H : Type*} [Fintype H] [DecidableEq H]

theorem exists_canonical_lie_unitary (R : LieMatrixCasimir.Generators d H)
    (mu : Fin d → ℕ) (hmu : Antitone mu) (v : H → ℂ) (hv : v ≠ 0)
    (hweight : ∀ i, R.E i i *ᵥ v = (mu i : ℂ) • v)
    (hraise : ∀ i j, i < j → R.E i j *ᵥ v = 0)
    (hcyc : LiePBW.cyclicSpan R v = ⊤) :
    ∃ W : Matrix (IrrepIndex mu) H ℂ, Wᴴ * W = 1 ∧ W * Wᴴ = 1 ∧
      ∀ i j, W * R.E i j = (irrepGenerators mu).E i j * W :=
  LiePBW.exists_highest_unitary R (irrepGenerators mu) (fun i => (mu i : ℂ))
    v (irrepHighest mu) hv (irrepHighest_ne_zero mu) hweight
    (irrepHighest_weight mu hmu) hraise (irrepHighest_raise mu) hcyc
    (irrepHighest_cyclic mu)

theorem exists_canonical_group_unitary
    (R : Matrix.unitaryGroup (Fin d) ℂ →* Matrix H H ℂ)
    (J : Matrix (Fin n → Fin d) H ℂ) (hJ : Jᴴ * J = 1)
    (hJR : ∀ U, SchurWeyl.physicalRepresentation d n U * J = J * R U)
    (mu : Fin d → ℕ) (hmu : Antitone mu) (hsize : tensorDegree mu = n)
    (v : H → ℂ) (hv : v ≠ 0)
    (hweight : ∀ i, (SchurWeyl.restrictedGenerators R J hJ hJR).E i i *ᵥ v =
      (mu i : ℂ) • v)
    (hraise : ∀ i j, i < j →
      (SchurWeyl.restrictedGenerators R J hJ hJR).E i j *ᵥ v = 0)
    (hcyc : LiePBW.cyclicSpan (SchurWeyl.restrictedGenerators R J hJ hJR) v = ⊤) :
    ∃ W : Matrix (IrrepIndex mu) H ℂ, Wᴴ * W = 1 ∧ W * Wᴴ = 1 ∧
      ∀ U, W * R U = irrepMatrix mu U * W := by
  subst n
  obtain ⟨W, hW, hW', hWE⟩ := exists_canonical_lie_unitary
    (SchurWeyl.restrictedGenerators R J hJ hJR) mu hmu v hv hweight hraise hcyc
  refine ⟨W, hW, hW', ?_⟩
  exact SchurWeyl.restricted_group_intertwiner_of_generators R (irrepMatrix mu)
    J (irrepTensorEmbedding mu) hJ (irrepTensorEmbedding_isometry mu) hJR
    (irrepTensorEmbedding_intertwines mu) W hWE

/-- Every constructed irreducible sector of the actual tensor-power unitary
representation is unitarily equivalent to the canonical exterior model of
an actual dominant occupation of the same tensor degree. -/
theorem exists_sector_canonical_unitary (i : SchurWeyl.Sector d n) :
    ∃ a : Occupation.Occupation d n, Antitone a.val ∧
      ∃ W : Matrix (IrrepIndex a.val) (SchurWeyl.SectorSpace d n i) ℂ,
        Wᴴ * W = 1 ∧ W * Wᴴ = 1 ∧ ∀ U,
          W * (SchurWeyl.physicalDecomposition d n).representation i U =
            irrepMatrix a.val U * W := by
  obtain ⟨a, v, hv, hmu, hweight, hraise, hcyc⟩ := SchurWeyl.exists_sector_highest i
  refine ⟨a, hmu, ?_⟩
  exact exists_canonical_group_unitary
    ((SchurWeyl.physicalDecomposition d n).representation i)
    ((SchurWeyl.physicalDecomposition d n).embedding i)
    ((SchurWeyl.physicalDecomposition d n).isometry i)
    ((SchurWeyl.physicalDecomposition d n).intertwines i) a.val hmu
    ((tensorDegree_eq_sum a.val hmu).trans a.property) v hv hweight hraise hcyc

end FreeEntropy
