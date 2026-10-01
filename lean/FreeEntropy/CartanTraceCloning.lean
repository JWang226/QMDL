/-
Copyright (c) 2026 Free Entropy formalization contributors.
See LICENSE and NOTICE in the repository root for license and attribution.
-/

import FreeEntropy.CartanCloning
import FreeEntropy.CasimirTrace
import FreeEntropy.TraceCloning

/-!
# Cloning channels from Casimir trace deficits

These adapters use actual isometries, sector projections and quantum channels.
The quantitative input is a Casimir operator gap and its compression on the
source sector. Equal shallow weight multiplicities transfer the trace error
between the two projections. No bound on their operator-norm distance occurs.
-/

noncomputable section
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator Kronecker
open Matrix FreeEntropy.OrbitMemory FreeEntropy.CloningMatrices
open FreeEntropy.CartanChannel FreeEntropy.CartanCloning

namespace FreeEntropy.CartanTraceCloning

set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 600000

variable {A B C T ι : Type*}
  [Fintype A] [Fintype B] [Fintype C] [Fintype T]
  [DecidableEq A] [DecidableEq B] [DecidableEq C] [DecidableEq T]

theorem trace_isometry_embedding (V : Matrix T C ℂ) (hV : Vᴴ * V = 1)
    (X : Matrix C C ℂ) : tr (V * X * Vᴴ) = tr X := by
  unfold tr
  rw [Matrix.trace_mul_cycle, hV, Matrix.one_mul]

theorem range_support_embedding (V : Matrix T C ℂ) (hV : Vᴴ * V = 1)
    (X : Matrix C C ℂ) : (V * Vᴴ) * (V * X * Vᴴ) = V * X * Vᴴ := by
  calc
    _ = V * (Vᴴ * V) * X * Vᴴ := by simp only [Matrix.mul_assoc]
    _ = _ := by rw [hV, Matrix.mul_one]

/-- Compressing a deficit back through its own sector isometry preserves
its trace. This supplies the link from ambient Casimir estimates to the
actual source/target block matrices. -/
theorem trace_compressed_deficit (V : Matrix T C ℂ) (hV : Vᴴ * V = 1)
    (X : Matrix C C ℂ) (Q : Matrix T T ℂ) :
    tr (X - Vᴴ * ((V * X * Vᴴ) * Q * (V * X * Vᴴ)) * V) =
      CasimirTrace.traceDeficit (V * X * Vᴴ) Q := by
  let P := V * X * Vᴴ
  have hRP : (V * Vᴴ) * P = P := range_support_embedding V hV X
  have hs : (V * Vᴴ) * (P - P * Q * P) = P - P * Q * P := by
    calc
      _ = (V * Vᴴ) * P - ((V * Vᴴ) * P) * Q * P := by
        simp only [Matrix.mul_sub, Matrix.mul_assoc]
      _ = _ := by rw [hRP]
  have ht : tr (Vᴴ * (P - P * Q * P) * V) = tr (P - P * Q * P) := by
    unfold tr
    rw [Matrix.trace_mul_cycle, hs]
  simpa only [Matrix.mul_sub, Matrix.sub_mul, P, isometry_pullback V hV,
    CasimirTrace.traceDeficit] using ht

/-- The trace-deficit version of `CartanCloning.ofWeightBlocks`. -/
def ofWeightBlocks (s : Finset ι) (m n : ι → ℕ) (pμ pν e : ι → ℝ)
    (Pμ : ι → Matrix A A ℂ) (Pν : ι → Matrix C C ℂ)
    (V : Matrix (A × B) C ℂ) (hV : Vᴴ * V = 1) (k : B)
    (din dout : ℝ) (hdin : 0 < din) (hdout : 0 < dout)
    (hbalance : partialTrace (V * Vᴴ) = (dout / din) • (1 : Matrix A A ℂ))
    (hpμ : ∀ i ∈ s, 0 ≤ pμ i) (hpν : ∀ i ∈ s, 0 ≤ pν i)
    (hPμ : ∀ i ∈ s, IsStarProjection (Pμ i))
    (hPν : ∀ i ∈ s, IsStarProjection (Pν i))
    (htrμ : ∀ i ∈ s, tr (Pμ i) = (m i : ℝ))
    (htrν : ∀ i ∈ s, tr (Pν i) = (n i : ℝ))
    (hnormμ : (mixture s pμ Pμ).trace = 1)
    (hnormν : (mixture s pν Pν).trace = 1)
    (hdefμ : ∀ i ∈ s,
      CasimirTrace.traceDeficit
        (basisEmbedding (A := A) k * Pμ i * (basisEmbedding (A := A) k)ᴴ)
        (V * Pν i * Vᴴ) ≤ e i * tr (Pμ i))
    (hdefν : ∀ i ∈ s,
      CasimirTrace.traceDeficit (V * Pν i * Vᴴ)
        (basisEmbedding (A := A) k * Pμ i * (basisEmbedding (A := A) k)ᴴ)
        ≤ e i * tr (Pν i))
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
    TraceCloning.TraceBlockRealization s m n pμ pν e (din / dout) A C := by
  let J := basisEmbedding (A := A) k
  let P : ι → Matrix (A × B) (A × B) ℂ := fun i => V * Pν i * Vᴴ
  let Q : ι → Matrix (A × B) (A × B) ℂ := fun i => J * Pμ i * Jᴴ
  have hJ : Jᴴ * J = 1 := basisEmbedding_isometry k
  have hP (i) (hi : i ∈ s) : IsStarProjection (P i) := isStarProjection_embedding V hV (hPν i hi)
  have hQ (i) (hi : i ∈ s) : IsStarProjection (Q i) := isStarProjection_embedding J hJ (hPμ i hi)
  have hμpos (i) (hi : i ∈ s) : (Pμ i).PosSemidef := (hPμ i hi).nonneg.posSemidef
  have hνpos (i) (hi : i ∈ s) : (Pν i).PosSemidef := (hPν i hi).nonneg.posSemidef
  refine {
    Pμ := Pμ
    Pν := Pν
    Cμ := fun i => Jᴴ * (Q i * P i * Q i) * J
    Cν := fun i => Vᴴ * (P i * Q i * P i) * V
    forward := cartanChannel V din dout hdin hdout hbalance
    reverse := reverseChannel V hV
    positive_μ := hμpos
    positive_ν := hνpos
    compressed_positive_ν := ?_
    trace_μ := htrμ
    trace_ν := htrν
    normalized_μ := hnormμ
    normalized_ν := hnormν
    deficit_positive_μ := ?_
    deficit_positive_ν := ?_
    deficit_trace_μ := ?_
    deficit_trace_ν := ?_
    branch_forward := ?_
    branch_reverse := ?_ }
  · intro i hi
    have h := (hQ i hi).nonneg.posSemidef.mul_mul_conjTranspose_same (P i)
    have hPH : (P i)ᴴ = P i := (hP i hi).isSelfAdjoint.star_eq
    rw [hPH] at h
    exact h.conjTranspose_mul_mul_same V
  · intro i hi
    have h := (CasimirTrace.projection_deficit_pos (hQ i hi) (hP i hi)).conjTranspose_mul_mul_same J
    simpa only [Matrix.mul_sub, Matrix.sub_mul, Q, isometry_pullback J hJ] using h
  · intro i hi
    have h := (CasimirTrace.projection_deficit_pos (hP i hi) (hQ i hi)).conjTranspose_mul_mul_same V
    simpa only [Matrix.mul_sub, Matrix.sub_mul, P, isometry_pullback V hV] using h
  · intro i hi
    rw [trace_compressed_deficit J hJ (Pμ i) (P i)]
    exact hdefμ i hi
  · intro i hi
    rw [trace_compressed_deficit V hV (Pν i) (Q i)]
    exact hdefν i hi
  · rw [cartanChannel_apply]
    have h := forward_branch_unembedded V hV k din dout (le_of_lt (div_pos hdin hdout))
      (mixture_positive s pμ Pμ hpμ hμpos)
    have hid : mixture s pμ (fun i => Vᴴ * (P i * Q i * P i) * V) =
        Vᴴ * J * mixture s pμ Pμ * Jᴴ * V := by
      calc
        _ = mixture s pμ (fun i => Vᴴ * Q i * V) := by
          apply Finset.sum_congr rfl
          intro i hi
          congr 1
          change Vᴴ * (P i * Q i * P i) * V = Vᴴ * Q i * V
          have hsector : (V * Vᴴ) * Q i * (V * Vᴴ) = P i * Q i * P i := hforward_sector i hi
          rw [← hsector, range_pullback V hV]
        _ = _ := by
          simp only [mixture, Q, Matrix.mul_sum, Matrix.sum_mul,
            Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc]
    rw [hid]
    exact h
  · rw [reverseChannel_apply]
    have h := reverse_retained_branch_le V k (mixture_positive s pν Pν hpν hνpos)
    have hid : mixture s pν (fun i => Jᴴ * (Q i * P i * Q i) * J) =
        Jᴴ * V * mixture s pν Pν * Vᴴ * J := by
      calc
        _ = mixture s pν (fun i => Jᴴ * P i * J) := by
          apply Finset.sum_congr rfl
          intro i hi
          congr 1
          exact (hreverse_sector i hi).symm
        _ = _ := by
          simp only [mixture, P, Matrix.mul_sum, Matrix.sum_mul,
            Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc]
    rw [hid]
    exact h


/-- Construct actual cloning channels and their trace-loss blocks from the
Casimir gap and compression. Equal weight multiplicities are used only when
the requested error coefficient is below one. Deeper sectors automatically
use the trivial positive trace-deficit bound. -/
def ofWeightBlocksOfCasimir (s : Finset ι) (m n : ι → ℕ) (pμ pν e : ι → ℝ)
    (Pμ : ι → Matrix A A ℂ) (Pν : ι → Matrix C C ℂ)
    (V : Matrix (A × B) C ℂ) (hV : Vᴴ * V = 1) (k : B)
    (din dout : ℝ) (hdin : 0 < din) (hdout : 0 < dout)
    (hbalance : partialTrace (V * Vᴴ) = (dout / din) • (1 : Matrix A A ℂ))
    (hpμ : ∀ i ∈ s, 0 ≤ pμ i) (hpν : ∀ i ∈ s, 0 ≤ pν i)
    (hPμ : ∀ i ∈ s, IsStarProjection (Pμ i))
    (hPν : ∀ i ∈ s, IsStarProjection (Pν i))
    (htrμ : ∀ i ∈ s, tr (Pμ i) = (m i : ℝ))
    (htrν : ∀ i ∈ s, tr (Pν i) = (n i : ℝ))
    (hnormμ : (mixture s pμ Pμ).trace = 1)
    (hnormν : (mixture s pν Pν).trace = 1)
    (K S : ι → Matrix (A × B) (A × B) ℂ) (gap deficit : ι → ℝ)
    (hshallow : ∀ i ∈ s, e i < 1 → m i = n i)
    (hgap : ∀ i ∈ s, e i < 1 → 0 < gap i)
    (hcasimir : ∀ i ∈ s, e i < 1 →
      gap i • (S i - V * Pν i * Vᴴ) ≤ K i)
    (hsupport : ∀ i ∈ s, e i < 1 →
      (basisEmbedding (A := A) k * Pμ i * (basisEmbedding (A := A) k)ᴴ) * S i *
        (basisEmbedding (A := A) k * Pμ i * (basisEmbedding (A := A) k)ᴴ) =
      basisEmbedding (A := A) k * Pμ i * (basisEmbedding (A := A) k)ᴴ)
    (hcompression : ∀ i ∈ s, e i < 1 →
      (basisEmbedding (A := A) k * Pμ i * (basisEmbedding (A := A) k)ᴴ) * K i *
        (basisEmbedding (A := A) k * Pμ i * (basisEmbedding (A := A) k)ᴴ) ≤
      deficit i • (basisEmbedding (A := A) k * Pμ i * (basisEmbedding (A := A) k)ᴴ))
    (hcoefficient : ∀ i ∈ s, e i < 1 → deficit i / gap i ≤ e i)
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
    TraceCloning.TraceBlockRealization s m n pμ pν e (din / dout) A C := by
  let J := basisEmbedding (A := A) k
  let P : ι → Matrix (A × B) (A × B) ℂ := fun i => V * Pν i * Vᴴ
  let Q : ι → Matrix (A × B) (A × B) ℂ := fun i => J * Pμ i * Jᴴ
  have hJ : Jᴴ * J = 1 := basisEmbedding_isometry k
  have hb (i : ι) (hi : i ∈ s) :
      CasimirTrace.traceDeficit (Q i) (P i) ≤ e i * tr (Pμ i) ∧
      CasimirTrace.traceDeficit (P i) (Q i) ≤ e i * tr (Pν i) := by
    have hP : IsStarProjection (P i) := isStarProjection_embedding V hV (hPν i hi)
    have hQ : IsStarProjection (Q i) := isStarProjection_embedding J hJ (hPμ i hi)
    have htP : tr (P i) = tr (Pν i) := trace_isometry_embedding V hV (Pν i)
    have htQ : tr (Q i) = tr (Pμ i) := trace_isometry_embedding J hJ (Pμ i)
    have hnμ : 0 ≤ tr (Pμ i) := by rw [htrμ i hi]; positivity
    have hnν : 0 ≤ tr (Pν i) := by rw [htrν i hi]; positivity
    by_cases he : e i < 1
    · have ht : tr (P i) = tr (Q i) := by
        rw [htP, htQ, htrν i hi, htrμ i hi, hshallow i hi he]
      have hr := CasimirTrace.reverse_traceDeficit_le_of_local_gap hQ (hsupport i hi he)
        (hgap i hi he) (hcasimir i hi he) (hcompression i hi he)
      have hf := CasimirTrace.forward_traceDeficit_le_of_local_gap hP hQ ht (hsupport i hi he)
        (hgap i hi he) (hcasimir i hi he) (hcompression i hi he)
      change CasimirTrace.traceDeficit (Q i) (P i) ≤
        (deficit i / gap i) * tr (Q i) at hr
      rw [htP] at hf
      rw [htQ] at hr
      exact ⟨hr.trans (mul_le_mul_of_nonneg_right (hcoefficient i hi he) hnμ),
        hf.trans (mul_le_mul_of_nonneg_right (hcoefficient i hi he) hnν)⟩
    · have hei : 1 ≤ e i := le_of_not_gt he
      have hr := CasimirTrace.traceDeficit_le_trace hQ hP
      have hf := CasimirTrace.traceDeficit_le_trace hP hQ
      rw [htQ] at hr
      rw [htP] at hf
      constructor
      · exact hr.trans (by nlinarith)
      · exact hf.trans (by nlinarith)
  exact ofWeightBlocks s m n pμ pν e Pμ Pν V hV k din dout hdin hdout hbalance
    hpμ hpν hPμ hPν htrμ htrν hnormμ hnormν
    (fun i hi => (hb i hi).1) (fun i hi => (hb i hi).2)
    hforward_sector hreverse_sector

/-- Genuine irreducibility and unitary intertwining also remove the channel
balance hypothesis. The conclusion is a concrete pair of quantum channels
with Casimir-controlled trace losses in the original source/target spaces. -/
def ofWeightBlocksOfCasimirOfIrreducible {G : Type*} [Group G] [Nonempty A] [Nonempty C]
    (UA : G →* Matrix A A ℂ) (UB : G →* Matrix B B ℂ) (UC : G →* Matrix C C ℂ)
    [Representation.IsIrreducible (Twirling.matrixRepresentation UA)]
    (hUA : ∀ g, (UA g)ᴴ * UA g = 1)
    (hUB : ∀ g, (UB g)ᴴ * UB g = 1)
    (hUC : ∀ g, (UC g)ᴴ * UC g = 1)
    (s : Finset ι) (m n : ι → ℕ) (pμ pν e : ι → ℝ)
    (Pμ : ι → Matrix A A ℂ) (Pν : ι → Matrix C C ℂ)
    (V : Matrix (A × B) C ℂ) (hV : Vᴴ * V = 1) (k : B)
    (hintertwine : ∀ g, (UA g ⊗ₖ UB g) * V = V * UC g)
    (hpμ : ∀ i ∈ s, 0 ≤ pμ i) (hpν : ∀ i ∈ s, 0 ≤ pν i)
    (hPμ : ∀ i ∈ s, IsStarProjection (Pμ i))
    (hPν : ∀ i ∈ s, IsStarProjection (Pν i))
    (htrμ : ∀ i ∈ s, tr (Pμ i) = (m i : ℝ))
    (htrν : ∀ i ∈ s, tr (Pν i) = (n i : ℝ))
    (hnormμ : (mixture s pμ Pμ).trace = 1)
    (hnormν : (mixture s pν Pν).trace = 1)
    (K S : ι → Matrix (A × B) (A × B) ℂ) (gap deficit : ι → ℝ)
    (hshallow : ∀ i ∈ s, e i < 1 → m i = n i)
    (hgap : ∀ i ∈ s, e i < 1 → 0 < gap i)
    (hcasimir : ∀ i ∈ s, e i < 1 →
      gap i • (S i - V * Pν i * Vᴴ) ≤ K i)
    (hsupport : ∀ i ∈ s, e i < 1 →
      (basisEmbedding (A := A) k * Pμ i * (basisEmbedding (A := A) k)ᴴ) * S i *
        (basisEmbedding (A := A) k * Pμ i * (basisEmbedding (A := A) k)ᴴ) =
      basisEmbedding (A := A) k * Pμ i * (basisEmbedding (A := A) k)ᴴ)
    (hcompression : ∀ i ∈ s, e i < 1 →
      (basisEmbedding (A := A) k * Pμ i * (basisEmbedding (A := A) k)ᴴ) * K i *
        (basisEmbedding (A := A) k * Pμ i * (basisEmbedding (A := A) k)ᴴ) ≤
      deficit i • (basisEmbedding (A := A) k * Pμ i * (basisEmbedding (A := A) k)ᴴ))
    (hcoefficient : ∀ i ∈ s, e i < 1 → deficit i / gap i ≤ e i)
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
    TraceCloning.TraceBlockRealization s m n pμ pν e ((Fintype.card A : ℝ) / (Fintype.card C : ℝ)) A C :=
  ofWeightBlocksOfCasimir s m n pμ pν e Pμ Pν V hV k
    (Fintype.card A : ℝ) (Fintype.card C : ℝ)
    (by exact_mod_cast (Fintype.card_pos : 0 < Fintype.card A))
    (by exact_mod_cast (Fintype.card_pos : 0 < Fintype.card C))
    (CartanBalance.balance_of_irreducible UA UB UC hUA hUB hUC V hV hintertwine)
    hpμ hpν hPμ hPν htrμ htrν hnormμ hnormν K S gap deficit
    hshallow hgap hcasimir hsupport hcompression hcoefficient hforward_sector hreverse_sector

/-- The manuscript's capped coefficient is obtained from shallow Casimir
gaps and compression alone. Deep sectors need no multiplicity equality or
Casimir assumption: integrality and `D ≥ 1` force their cap to be one. -/
def ofCappedCasimirWeightBlocksOfIrreducible {G : Type*} [Group G] [Nonempty A] [Nonempty C]
    (UA : G →* Matrix A A ℂ) (UB : G →* Matrix B B ℂ) (UC : G →* Matrix C C ℂ)
    [Representation.IsIrreducible (Twirling.matrixRepresentation UA)]
    (hUA : ∀ g, (UA g)ᴴ * UA g = 1)
    (hUB : ∀ g, (UB g)ᴴ * UB g = 1)
    (hUC : ∀ g, (UC g)ᴴ * UC g = 1)
    (s : Finset ι) (depth m n : ι → ℕ) (pμ pν : ι → ℝ)
    (D g : ℕ) (hD : 1 ≤ D)
    (Pμ : ι → Matrix A A ℂ) (Pν : ι → Matrix C C ℂ)
    (V : Matrix (A × B) C ℂ) (hV : Vᴴ * V = 1) (k : B)
    (hintertwine : ∀ g, (UA g ⊗ₖ UB g) * V = V * UC g)
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
  apply ofWeightBlocksOfCasimirOfIrreducible UA UB UC hUA hUB hUC
    s m n pμ pν e Pμ Pν V hV k hintertwine hpμ hpν hPμ hPν htrμ htrν
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
