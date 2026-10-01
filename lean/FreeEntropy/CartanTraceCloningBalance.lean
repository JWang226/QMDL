/-
Copyright (c) 2026 Free Entropy formalization contributors.
See LICENSE and NOTICE in the repository root for license and attribution.
-/

import FreeEntropy.CartanTraceCloning

/-! Capped Casimir cloning estimates with an explicit normalization identity.
The Lie-only adapter supplies this identity without any group data. -/
noncomputable section
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator Kronecker
open Matrix FreeEntropy.OrbitMemory FreeEntropy.CloningMatrices
open FreeEntropy.CartanChannel FreeEntropy.CartanCloning
namespace FreeEntropy.CartanTraceCloning
set_option backward.isDefEq.respectTransparency false
variable {A B C ι : Type*} [Fintype A] [Fintype B] [Fintype C]
  [DecidableEq A] [DecidableEq B] [DecidableEq C]

def ofCappedCasimirWeightBlocks [Nonempty A] [Nonempty C]
    (s : Finset ι) (depth m n : ι → ℕ) (pμ pν : ι → ℝ)
    (D g : ℕ) (hD : 1 ≤ D)
    (Pμ : ι → Matrix A A ℂ) (Pν : ι → Matrix C C ℂ)
    (V : Matrix (A × B) C ℂ) (hV : Vᴴ * V = 1) (k : B)
    (hbalance : partialTrace (V * Vᴴ) =
      ((Fintype.card C : ℝ) / (Fintype.card A : ℝ)) • (1 : Matrix A A ℂ))
    (hpμ : ∀ i ∈ s, 0 ≤ pμ i) (hpν : ∀ i ∈ s, 0 ≤ pν i)
    (hPμ : ∀ i ∈ s, IsStarProjection (Pμ i))
    (hPν : ∀ i ∈ s, IsStarProjection (Pν i))
    (htrμ : ∀ i ∈ s, tr (Pμ i) = (m i : ℝ))
    (htrν : ∀ i ∈ s, tr (Pν i) = (n i : ℝ))
    (hnormμ : (mixture s pμ Pμ).trace = 1)
    (hnormν : (mixture s pν Pν).trace = 1)
    (K S : ι → Matrix (A × B) (A × B) ℂ) (deficit : ι → ℝ)
    (hshallow : ∀ i ∈ s, depth i ≤ g → m i = n i)
    (hcasimir : ∀ i ∈ s, depth i ≤ g →
      ((g : ℝ) + 2) • (S i - V * Pν i * Vᴴ) ≤ K i)
    (hsupport : ∀ i ∈ s, depth i ≤ g →
      (basisEmbedding (A := A) k * Pμ i * (basisEmbedding (A := A) k)ᴴ) * S i *
        (basisEmbedding (A := A) k * Pμ i * (basisEmbedding (A := A) k)ᴴ) =
      basisEmbedding (A := A) k * Pμ i * (basisEmbedding (A := A) k)ᴴ)
    (hcompression : ∀ i ∈ s, depth i ≤ g →
      (basisEmbedding (A := A) k * Pμ i * (basisEmbedding (A := A) k)ᴴ) * K i *
        (basisEmbedding (A := A) k * Pμ i * (basisEmbedding (A := A) k)ᴴ) ≤
      deficit i • (basisEmbedding (A := A) k * Pμ i * (basisEmbedding (A := A) k)ᴴ))
    (hdeficit : ∀ i ∈ s, depth i ≤ g →
      deficit i ≤ 2 * (depth i : ℝ) * (D : ℝ))
    (hforward_sector : ∀ i ∈ s,
      (V * Vᴴ) * (basisEmbedding (A := A) k * Pμ i * (basisEmbedding (A := A) k)ᴴ) * (V * Vᴴ) =
      (V * Pν i * Vᴴ) * (basisEmbedding (A := A) k * Pμ i * (basisEmbedding (A := A) k)ᴴ) *
        (V * Pν i * Vᴴ))
    (hreverse_sector : ∀ i ∈ s,
      (basisEmbedding (A := A) k)ᴴ * (V * Pν i * Vᴴ) * basisEmbedding (A := A) k =
      (basisEmbedding (A := A) k)ᴴ *
        ((basisEmbedding (A := A) k * Pμ i * (basisEmbedding (A := A) k)ᴴ) *
          (V * Pν i * Vᴴ) * (basisEmbedding (A := A) k * Pμ i * (basisEmbedding (A := A) k)ᴴ)) *
        basisEmbedding (A := A) k) :
    TraceCloning.TraceBlockRealization s m n pμ pν
      (fun i => min 1 (2 * (depth i : ℝ) * (D : ℝ) / ((g : ℝ) + 2)))
      ((Fintype.card A : ℝ) / (Fintype.card C : ℝ)) A C := by
  let e : ι → ℝ := fun i => min 1 (2 * (depth i : ℝ) * (D : ℝ) / ((g : ℝ) + 2))
  have hsmall (i : ι) (he : e i < 1) : depth i ≤ g := by
    by_contra h
    have hc := Cloning.deficit_cap_eq_one_of_deep (depth i) g (D : ℝ)
      (by exact_mod_cast hD) (Nat.lt_of_not_ge h)
    change min 1 (2 * (depth i : ℝ) * (D : ℝ) / ((g : ℝ) + 2)) < 1 at he
    rw [hc] at he
    exact (lt_irrefl 1) he
  apply ofWeightBlocksOfCasimir s m n pμ pν e Pμ Pν V hV k
    (Fintype.card A : ℝ) (Fintype.card C : ℝ)
    (by exact_mod_cast (Fintype.card_pos : 0 < Fintype.card A))
    (by exact_mod_cast (Fintype.card_pos : 0 < Fintype.card C))
    hbalance hpμ hpν hPμ hPν htrμ htrν
    hnormμ hnormν K S (fun _ => (g : ℝ) + 2) deficit
    (fun i hi he => hshallow i hi (hsmall i he))
    (fun _ _ _ => by positivity)
    (fun i hi he => hcasimir i hi (hsmall i he))
    (fun i hi he => hsupport i hi (hsmall i he))
    (fun i hi he => hcompression i hi (hsmall i he))
    ?_ hforward_sector hreverse_sector
  intro i hi he
  have hx : 2 * (depth i : ℝ) * (D : ℝ) / ((g : ℝ) + 2) < 1 := by
    simpa only [e, min_lt_iff, lt_self_iff_false, false_or] using he
  change deficit i / ((g : ℝ) + 2) ≤
    min 1 (2 * (depth i : ℝ) * (D : ℝ) / ((g : ℝ) + 2))
  rw [min_eq_right hx.le]
  exact (div_le_div_iff_of_pos_right (by positivity : 0 < (g : ℝ) + 2)).mpr
    (hdeficit i hi (hsmall i he))

end FreeEntropy.CartanTraceCloning
