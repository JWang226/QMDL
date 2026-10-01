/-
Copyright (c) 2026 Free Entropy formalization contributors.
See LICENSE and NOTICE in the repository root for license and attribution.
-/

import FreeEntropy.Channels
import Mathlib.Analysis.Matrix.Order
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic.FieldSimp

/-!
# The Cartan formula is a completely positive trace-preserving map

The forward slice/Kraus proofs and basic partial-trace identities are adapted
from the existing local `Cloning-github/formalization/Cloning/` files
`CartanChannel.lean`, `Compression.lean`, and
`MatrixPartialTraceCovariance.lean`. Those files were not modified.
The reverse-channel construction and adjoint connection below extend that
ported algebra inside the separately compiled FreeEntropy project.

We construct actual Kraus matrices from the slices of the Cartan inclusion.
The partial-trace balance is the explicit representation-theoretic input needed
for trace preservation; all matrix algebra and complete positivity are proved.
-/

noncomputable section
open scoped BigOperators Matrix Kronecker ComplexOrder MatrixOrder
open Matrix
namespace FreeEntropy.CartanChannel
open FreeEntropy.Channels

variable {A B C : Type*} [Fintype A] [Fintype B] [Fintype C]
variable [DecidableEq A] [DecidableEq B] [DecidableEq C]
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false

/-- The explicit Cartan-channel formula, before any channel-property assertions. -/
def sectorMap (din dout : ℝ) (V : Matrix (A × B) C ℂ) (X : Matrix A A ℂ) :
    Matrix C C ℂ :=
  (din / dout) • (V.conjTranspose * (X ⊗ₖ (1 : Matrix B B ℂ)) * V)

/-- Partial trace over the second finite matrix index. -/
def partialTrace (Y : Matrix (A × B) (A × B) ℂ) : Matrix A A ℂ :=
  fun i j => ∑ k, Y (i, k) (j, k)

/-- Defining trace-pairing identity for the finite-dimensional partial trace. -/
lemma trace_tensor_pairing (X : Matrix A A ℂ) (Y : Matrix (A × B) (A × B) ℂ) :
    Matrix.trace ((X ⊗ₖ (1 : Matrix B B ℂ)) * Y) =
      Matrix.trace (X * partialTrace Y) := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.kronecker_apply,
    Matrix.one_apply, partialTrace, Fintype.sum_prod_type, Finset.mul_sum]
  simp only [mul_ite, mul_one, mul_zero, ite_mul, zero_mul]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true]
  apply Finset.sum_congr rfl
  intro i _
  exact Finset.sum_comm

/-- A Kraus matrix obtained by contracting the environment leg of the inclusion. -/
def sliceKraus (V : Matrix (A × B) C ℂ) (k : B) : Matrix C A ℂ :=
  fun i j => star (V (j, k) i)

lemma core_eq_kraus (V : Matrix (A × B) C ℂ) (X : Matrix A A ℂ) :
    V.conjTranspose * (X ⊗ₖ (1 : Matrix B B ℂ)) * V = krausMap (sliceKraus V) X := by
  ext i j
  simp only [krausMap, sliceKraus, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Matrix.kronecker_apply, Matrix.one_apply, Fintype.sum_prod_type,
    Matrix.sum_apply, star_star, Finset.sum_mul]
  simp only [mul_ite, mul_one, mul_zero, ite_mul, zero_mul, Finset.sum_ite_eq',
    Finset.mem_univ, if_true]
  exact Finset.sum_comm

/-- The Kraus normalization operator is the environment partial trace. -/
lemma slice_normalization (V : Matrix (A × B) C ℂ) :
    (∑ k, (sliceKraus V k).conjTranspose * sliceKraus V k) =
      partialTrace (V * V.conjTranspose) := by
  ext i j
  simp [sliceKraus, partialTrace, Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply]

/-- Scaling all Kraus operators by √r scales the represented map by r. -/
lemma krausMap_sqrt_smul {ι : Type*} [Fintype ι]
    (K : ι → Matrix C A ℂ) (X : Matrix A A ℂ) (r : ℝ) (hr : 0 ≤ r) :
    krausMap (fun i => Real.sqrt r • K i) X = r • krausMap K X := by
  simp only [krausMap, Matrix.conjTranspose_smul, star_trivial]
  simp_rw [(Matrix.smul_mul (R := ℝ)), (Matrix.mul_smul (R := ℝ)), smul_smul, Real.mul_self_sqrt hr]
  exact (Finset.smul_sum ..).symm

/-- Explicit Kraus operators for the Cartan-sector formula. -/
def cartanKraus (V : Matrix (A × B) C ℂ) (din dout : ℝ) (k : B) : Matrix C A ℂ :=
  Real.sqrt (din / dout) • sliceKraus V k

lemma sectorMap_eq_kraus (V : Matrix (A × B) C ℂ) (X : Matrix A A ℂ)
    (din dout : ℝ) (hr : 0 ≤ din / dout) :
    sectorMap din dout V X = krausMap (cartanKraus V din dout) X := by
  rw [sectorMap, core_eq_kraus]
  exact (krausMap_sqrt_smul (sliceKraus V) X (din / dout) hr).symm

/-- The Cartan-sector formula is positive at every finite amplification. -/
lemma sectorMap_completely_positive {κ : Type*} [Fintype κ] [DecidableEq κ]
    (V : Matrix (A × B) C ℂ) (din dout : ℝ) (hr : 0 ≤ din / dout)
    {X : Matrix (κ × A) (κ × A) ℂ} (hX : X.PosSemidef) :
    (amplify (sectorMap din dout V) X).PosSemidef := by
  have heq : sectorMap din dout V = krausMap (cartanKraus V din dout) := by
    funext Y
    exact sectorMap_eq_kraus V Y din dout hr
  rw [heq]
  exact krausMap_completely_positive _ hX

lemma cartanKraus_normalization (V : Matrix (A × B) C ℂ) (din dout : ℝ)
    (hdin : 0 < din) (hdout : 0 < dout)
    (hbalance : partialTrace (V * V.conjTranspose) = (dout / din) • (1 : Matrix A A ℂ)) :
    (∑ k, (cartanKraus V din dout k).conjTranspose * cartanKraus V din dout k) = 1 := by
  have hr : 0 ≤ din / dout := le_of_lt (div_pos hdin hdout)
  simp only [cartanKraus, Matrix.conjTranspose_smul, star_trivial,
    (Matrix.smul_mul (R := ℝ)), (Matrix.mul_smul (R := ℝ)), smul_smul, Real.mul_self_sqrt hr]
  rw [← Finset.smul_sum, slice_normalization, hbalance, smul_smul]
  have hc : din / dout * (dout / din) = 1 := by
    field_simp
  rw [hc, one_smul]

/-- A concrete channel realizing the Cartan formula. The balance identity is
exactly the input supplied by irreducibility and Schur's lemma in the paper. -/
def cartanChannel (V : Matrix (A × B) C ℂ) (din dout : ℝ)
    (hdin : 0 < din) (hdout : 0 < dout)
    (hbalance : partialTrace (V * V.conjTranspose) = (dout / din) • (1 : Matrix A A ℂ)) :
    MatrixChannel A C :=
  ofKraus (cartanKraus V din dout) (cartanKraus_normalization V din dout hdin hdout hbalance)

lemma cartanChannel_apply (V : Matrix (A × B) C ℂ) (din dout : ℝ)
    (hdin : 0 < din) (hdout : 0 < dout)
    (hbalance : partialTrace (V * V.conjTranspose) = (dout / din) • (1 : Matrix A A ℂ))
    (X : Matrix A A ℂ) :
    (cartanChannel V din dout hdin hdout hbalance).toFun X = sectorMap din dout V X := by
  exact (sectorMap_eq_kraus V X din dout (le_of_lt (div_pos hdin hdout))).symm

/-- Reverse Kraus matrices are the slices of the isometric inclusion itself. -/
def reverseKraus (V : Matrix (A × B) C ℂ) (k : B) : Matrix A C ℂ :=
  fun i j => V (i, k) j

/-- The reverse Cartan map is the partial trace of the isometric embedding. -/
def reverseMap (V : Matrix (A × B) C ℂ) (Y : Matrix C C ℂ) : Matrix A A ℂ :=
  partialTrace (V * Y * V.conjTranspose)

theorem reverseMap_eq_kraus (V : Matrix (A × B) C ℂ) (Y : Matrix C C ℂ) :
    reverseMap V Y = krausMap (reverseKraus V) Y := by
  ext i j
  simp [reverseMap, partialTrace, krausMap, reverseKraus, Matrix.mul_apply,
    Matrix.conjTranspose_apply, Matrix.sum_apply]

/-- An isometry normalizes the reverse Kraus family exactly. -/
theorem reverseKraus_normalization (V : Matrix (A × B) C ℂ) :
    (∑ k, (reverseKraus V k).conjTranspose * reverseKraus V k) =
      V.conjTranspose * V := by
  ext i j
  simp only [reverseKraus, Matrix.sum_apply, Matrix.mul_apply,
    Matrix.conjTranspose_apply, Fintype.sum_prod_type]
  exact Finset.sum_comm

/-- The reverse map is CPTP whenever the Cartan inclusion is isometric. -/
def reverseChannel (V : Matrix (A × B) C ℂ) (hV : V.conjTranspose * V = 1) :
    MatrixChannel C A :=
  ofKraus (reverseKraus V) ((reverseKraus_normalization V).trans hV)

theorem reverseChannel_apply (V : Matrix (A × B) C ℂ)
    (hV : V.conjTranspose * V = 1) (Y : Matrix C C ℂ) :
    (reverseChannel V hV).toFun Y = partialTrace (V * Y * V.conjTranspose) :=
  (reverseMap_eq_kraus V Y).symm

/-- The ordinary environment partial trace is itself a concrete channel. -/
def partialTraceChannel : MatrixChannel (A × B) A :=
  reverseChannel (1 : Matrix (A × B) (A × B) ℂ) (by simp)

theorem partialTraceChannel_apply (Y : Matrix (A × B) (A × B) ℂ) :
    (partialTraceChannel (A := A) (B := B)).toFun Y = partialTrace Y := by
  rw [partialTraceChannel, reverseChannel_apply]
  simp

/-- Isometric embedding is a concrete single-Kraus channel. -/
def embeddingChannel (V : Matrix (A × B) C ℂ) (hV : V.conjTranspose * V = 1) :
    MatrixChannel C (A × B) :=
  ofKraus (fun _ : Unit => V) (by simpa using hV)

theorem embeddingChannel_apply (V : Matrix (A × B) C ℂ)
    (hV : V.conjTranspose * V = 1) (Y : Matrix C C ℂ) :
    (embeddingChannel V hV).toFun Y = V * Y * V.conjTranspose := by
  simp [embeddingChannel, ofKraus, krausMap]

/-- The concrete trace adjoint of the forward formula. -/
def sectorAdjoint (din dout : ℝ) (V : Matrix (A × B) C ℂ)
    (Y : Matrix C C ℂ) : Matrix A A ℂ :=
  (din / dout) • reverseMap V Y

/-- Defining adjoint equality for every pair of matrices. -/
theorem sectorMap_trace_pairing (V : Matrix (A × B) C ℂ)
    (din dout : ℝ) (X : Matrix A A ℂ) (Y : Matrix C C ℂ) :
    Matrix.trace (sectorMap din dout V X * Y) =
      Matrix.trace (X * sectorAdjoint din dout V Y) := by
  unfold sectorMap sectorAdjoint reverseMap
  rw [Matrix.smul_mul, Matrix.trace_smul, Matrix.mul_smul, Matrix.trace_smul]
  congr 1
  calc
    _ = Matrix.trace ((X ⊗ₖ (1 : Matrix B B ℂ)) * (V * Y * V.conjTranspose)) := by
      rw [Matrix.mul_assoc, Matrix.mul_assoc, Matrix.trace_mul_comm V.conjTranspose]
      simp only [Matrix.mul_assoc]
    _ = _ := trace_tensor_pairing _ _

/-- The forward formula commutes with conjugate transpose. -/
theorem sectorMap_conjTranspose (V : Matrix (A × B) C ℂ)
    (din dout : ℝ) (X : Matrix A A ℂ) :
    (sectorMap din dout V X).conjTranspose = sectorMap din dout V X.conjTranspose := by
  simp only [sectorMap, Matrix.conjTranspose_smul, star_trivial,
    Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
    Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one, Matrix.mul_assoc]

/-- The same adjoint is the Hilbert--Schmidt adjoint, expressed without
introducing a second matrix inner-product structure. -/
theorem sectorMap_hilbertSchmidt_pairing (V : Matrix (A × B) C ℂ)
    (din dout : ℝ) (X : Matrix A A ℂ) (Y : Matrix C C ℂ) :
    Matrix.trace ((sectorMap din dout V X).conjTranspose * Y) =
      Matrix.trace (X.conjTranspose * sectorAdjoint din dout V Y) := by
  rw [sectorMap_conjTranspose]
  exact sectorMap_trace_pairing V din dout _ Y

/-- Taking the adjoint and multiplying by the inverse dimension ratio gives
the reverse partial-trace map; both dimension factors cancel. -/
theorem normalized_adjoint_eq_reverse (V : Matrix (A × B) C ℂ)
    (din dout : ℝ) (hdin : din ≠ 0) (hdout : dout ≠ 0) (Y : Matrix C C ℂ) :
    (dout / din) • sectorAdjoint din dout V Y = reverseMap V Y := by
  rw [sectorAdjoint, smul_smul]
  have hscalar : dout / din * (din / dout) = 1 := by field_simp
  rw [hscalar, one_smul]

/-- The embedded forward channel is compression to the Cartan range.
This is equation `embedded_channel` in the manuscript. -/
theorem embedded_sectorMap (V : Matrix (A × B) C ℂ)
    (din dout : ℝ) (X : Matrix A A ℂ) :
    V * sectorMap din dout V X * V.conjTranspose =
      (din / dout) • ((V * V.conjTranspose) * (X ⊗ₖ (1 : Matrix B B ℂ)) *
        (V * V.conjTranspose)) := by
  simp only [sectorMap, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc]

/-- Isometry identifies the image of the maximally mixed state. -/
theorem sectorMap_maximally_mixed (V : Matrix (A × B) C ℂ)
    (din dout : ℝ) (hdin : din ≠ 0) (hV : V.conjTranspose * V = 1) :
    sectorMap din dout V ((1 / din) • (1 : Matrix A A ℂ)) =
      (1 / dout) • (1 : Matrix C C ℂ) := by
  unfold sectorMap
  rw [Matrix.smul_kronecker, Matrix.one_kronecker_one, Matrix.mul_smul,
    Matrix.smul_mul, Matrix.mul_one, hV, smul_smul]
  congr 1
  field_simp

/-- Partial trace preserves the ordinary trace. -/
theorem trace_partialTrace (Y : Matrix (A × B) (A × B) ℂ) :
    Matrix.trace (partialTrace Y) = Matrix.trace Y := by
  simp [partialTrace, Matrix.trace, Matrix.diag, Fintype.sum_prod_type]

/-- Schur's lemma only needs to supply scalarity of the partial trace.
The coefficient then follows from the isometry and the actual dimensions. -/
theorem balance_of_scalar [Nonempty A] (V : Matrix (A × B) C ℂ)
    (hV : V.conjTranspose * V = 1) (c : ℝ)
    (hscalar : partialTrace (V * V.conjTranspose) = c • (1 : Matrix A A ℂ)) :
    partialTrace (V * V.conjTranspose) =
      ((Fintype.card C : ℝ) / (Fintype.card A : ℝ)) • (1 : Matrix A A ℂ) := by
  have ht : (Matrix.trace (partialTrace (V * V.conjTranspose))).re =
      (Matrix.trace (c • (1 : Matrix A A ℂ))).re :=
    congrArg (fun X : Matrix A A ℂ => (Matrix.trace X).re) hscalar
  rw [trace_partialTrace, Matrix.trace_mul_comm V, hV] at ht
  simp only [Matrix.trace_smul, Matrix.trace_one] at ht
  have hreal : (Fintype.card C : ℝ) = c * (Fintype.card A : ℝ) := by
    simpa using ht
  have hd : (Fintype.card A : ℝ) ≠ 0 := by exact_mod_cast (Fintype.card_ne_zero : Fintype.card A ≠ 0)
  have hc : c = (Fintype.card C : ℝ) / (Fintype.card A : ℝ) :=
    (eq_div_iff hd).mpr hreal.symm
  rwa [← hc]

/-- Actual-dimension forward channel with scalarity, rather than the exact
dimension balance, as its remaining representation-theoretic input. -/
def cartanChannelOfScalar [Nonempty A] [Nonempty C]
    (V : Matrix (A × B) C ℂ) (hV : V.conjTranspose * V = 1)
    (c : ℝ) (hscalar : partialTrace (V * V.conjTranspose) = c • (1 : Matrix A A ℂ)) :
    MatrixChannel A C :=
  cartanChannel V (Fintype.card A : ℝ) (Fintype.card C : ℝ)
    (by exact_mod_cast (Fintype.card_pos : 0 < Fintype.card A))
    (by exact_mod_cast (Fintype.card_pos : 0 < Fintype.card C))
    (balance_of_scalar V hV c hscalar)

/-- A spectator unitary cancels under partial trace. The proof is adapted
from the sibling project's `MatrixPartialTraceCovariance.lean`. -/
theorem partialTrace_tensor_conjugation (U : Matrix A A ℂ) (W : Matrix B B ℂ)
    (X : Matrix (A × B) (A × B) ℂ) (hW : W.conjTranspose * W = 1) :
    partialTrace ((U ⊗ₖ W) * X * (U ⊗ₖ W).conjTranspose) =
      U * partialTrace X * U.conjTranspose := by
  apply Matrix.ext_iff_trace_mul_left.mpr
  intro T
  have htest : (U ⊗ₖ W).conjTranspose * (T ⊗ₖ (1 : Matrix B B ℂ)) *
      (U ⊗ₖ W) = (U.conjTranspose * T * U) ⊗ₖ (1 : Matrix B B ℂ) := by
    rw [Matrix.conjTranspose_kronecker, ← Matrix.mul_kronecker_mul,
      ← Matrix.mul_kronecker_mul]
    simp only [Matrix.mul_one, hW]
  calc
    _ = Matrix.trace ((T ⊗ₖ (1 : Matrix B B ℂ)) *
        ((U ⊗ₖ W) * X * (U ⊗ₖ W).conjTranspose)) := (trace_tensor_pairing T _).symm
    _ = Matrix.trace (((U ⊗ₖ W).conjTranspose *
        (T ⊗ₖ (1 : Matrix B B ℂ)) * (U ⊗ₖ W)) * X) := by
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.trace_mul_cycle]
      simp only [Matrix.mul_assoc]
    _ = Matrix.trace (((U.conjTranspose * T * U) ⊗ₖ (1 : Matrix B B ℂ)) * X) := by
      rw [htest]
    _ = Matrix.trace ((U.conjTranspose * T * U) * partialTrace X) := trace_tensor_pairing _ X
    _ = Matrix.trace (T * (U * partialTrace X * U.conjTranspose)) := by
      simp only [Matrix.mul_assoc]
      rw [Matrix.trace_mul_comm U.conjTranspose]
      simp only [Matrix.mul_assoc]

/-- Intertwining proves covariance of the actual reverse channel formula. -/
theorem reverseMap_covariant (U : Matrix A A ℂ) (W : Matrix B B ℂ)
    (Z : Matrix C C ℂ) (V : Matrix (A × B) C ℂ)
    (hW : W.conjTranspose * W = 1) (hintertwine : (U ⊗ₖ W) * V = V * Z)
    (Y : Matrix C C ℂ) :
    reverseMap V (Z * Y * Z.conjTranspose) = U * reverseMap V Y * U.conjTranspose := by
  unfold reverseMap
  calc
    _ = partialTrace ((V * Z) * Y * (V * Z).conjTranspose) := by
      simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    _ = partialTrace (((U ⊗ₖ W) * V) * Y * ((U ⊗ₖ W) * V).conjTranspose) := by
      rw [hintertwine]
    _ = partialTrace ((U ⊗ₖ W) * (V * Y * V.conjTranspose) * (U ⊗ₖ W).conjTranspose) := by
      simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    _ = _ := partialTrace_tensor_conjugation U W _ hW

/-- Intertwining and unitarity prove covariance of the forward Cartan formula. -/
theorem sectorMap_covariant (U : Matrix A A ℂ) (W : Matrix B B ℂ)
    (Z : Matrix C C ℂ) (V : Matrix (A × B) C ℂ)
    (hU : U.conjTranspose * U = 1) (hW : W.conjTranspose * W = 1)
    (hZ : Z * Z.conjTranspose = 1) (hintertwine : (U ⊗ₖ W) * V = V * Z)
    (din dout : ℝ) (X : Matrix A A ℂ) :
    sectorMap din dout V (U * X * U.conjTranspose) =
      Z * sectorMap din dout V X * Z.conjTranspose := by
  have hT : (U ⊗ₖ W).conjTranspose * (U ⊗ₖ W) = 1 := by
    rw [Matrix.conjTranspose_kronecker, ← Matrix.mul_kronecker_mul, hU, hW,
      Matrix.one_kronecker_one]
  have hinverse : (U ⊗ₖ W).conjTranspose * V = V * Z.conjTranspose := by
    calc
      _ = ((U ⊗ₖ W).conjTranspose * V) * (Z * Z.conjTranspose) := by rw [hZ, Matrix.mul_one]
      _ = (U ⊗ₖ W).conjTranspose * (V * Z) * Z.conjTranspose := by simp only [Matrix.mul_assoc]
      _ = (U ⊗ₖ W).conjTranspose * ((U ⊗ₖ W) * V) * Z.conjTranspose := by rw [hintertwine]
      _ = _ := by rw [← Matrix.mul_assoc, hT, Matrix.one_mul]
  have hleft : V.conjTranspose * (U ⊗ₖ W) = Z * V.conjTranspose := by
    simpa only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose] using
      congrArg Matrix.conjTranspose hinverse
  have hWright : W * W.conjTranspose = 1 := mul_eq_one_comm.mp hW
  have htensor : (U * X * U.conjTranspose) ⊗ₖ (1 : Matrix B B ℂ) =
      (U ⊗ₖ W) * (X ⊗ₖ (1 : Matrix B B ℂ)) * (U ⊗ₖ W).conjTranspose := by
    rw [Matrix.conjTranspose_kronecker, ← Matrix.mul_kronecker_mul,
      ← Matrix.mul_kronecker_mul]
    simp only [Matrix.mul_one, hWright]
  unfold sectorMap
  rw [htensor, Matrix.mul_smul, Matrix.smul_mul]
  congr 1
  calc
    _ = (V.conjTranspose * (U ⊗ₖ W)) * (X ⊗ₖ (1 : Matrix B B ℂ)) *
        ((U ⊗ₖ W).conjTranspose * V) := by simp only [Matrix.mul_assoc]
    _ = (Z * V.conjTranspose) * (X ⊗ₖ (1 : Matrix B B ℂ)) * (V * Z.conjTranspose) := by
      rw [hleft, hinverse]
    _ = _ := by simp only [Matrix.mul_assoc]

/-- Inclusion with the environment fixed at the selected orthonormal basis
vector. In the application, this vector is the auxiliary highest weight. -/
def basisEmbedding (k : B) : Matrix (A × B) A ℂ :=
  fun p i => if p.2 = k then (1 : Matrix A A ℂ) p.1 i else 0

theorem basisEmbedding_isometry (k : B) :
    (basisEmbedding (A := A) k).conjTranspose * basisEmbedding (A := A) k = 1 := by
  ext i j
  simp [basisEmbedding, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Matrix.one_apply, Fintype.sum_prod_type, apply_ite, eq_comm]

/-- The forward Kraus slice is compression against the chosen environment
line. This identifies the algebraic Kraus branch with the geometric one. -/
theorem sliceKraus_eq_compression (V : Matrix (A × B) C ℂ) (k : B) :
    sliceKraus V k = V.conjTranspose * basisEmbedding (A := A) k := by
  ext i j
  simp [sliceKraus, basisEmbedding, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Matrix.one_apply, Fintype.sum_prod_type, apply_ite]

theorem reverseKraus_eq_compression (V : Matrix (A × B) C ℂ) (k : B) :
    reverseKraus V k = (basisEmbedding (A := A) k).conjTranspose * V := by
  ext i j
  simp [reverseKraus, basisEmbedding, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Matrix.one_apply, Fintype.sum_prod_type, apply_ite]

/-- Exact identification of the embedded retained forward branch with
`a P J σ J† P`, where `a=din/dout`, `P=VV†`, and `J` fixes the environment. -/
theorem embedded_cartan_branch (V : Matrix (A × B) C ℂ) (k : B)
    (din dout : ℝ) (hr : 0 ≤ din / dout) (σ : Matrix A A ℂ) :
    V * (cartanKraus V din dout k * σ * (cartanKraus V din dout k).conjTranspose) *
        V.conjTranspose =
      (din / dout) • ((V * V.conjTranspose) * basisEmbedding (A := A) k * σ *
        (basisEmbedding (A := A) k).conjTranspose * (V * V.conjTranspose)) := by
  simp only [cartanKraus, Matrix.conjTranspose_smul, star_trivial,
    (Matrix.smul_mul (R := ℝ)), (Matrix.mul_smul (R := ℝ)), smul_smul,
    Real.mul_self_sqrt hr]
  rw [sliceKraus_eq_compression]
  simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]

/-- A PSD input allows retention of the highest-weight branch in the actual
embedded forward Cartan output. No projector comparison is assumed. -/
theorem forward_retained_branch_le (V : Matrix (A × B) C ℂ) (k : B)
    (din dout : ℝ) (hr : 0 ≤ din / dout)
    {σ : Matrix A A ℂ} (hσ : σ.PosSemidef) :
    (din / dout) • ((V * V.conjTranspose) * basisEmbedding (A := A) k * σ *
      (basisEmbedding (A := A) k).conjTranspose * (V * V.conjTranspose)) ≤
        V * sectorMap din dout V σ * V.conjTranspose := by
  have h := krausMap_sub_branch_positive (cartanKraus V din dout) k hσ
  rw [← sectorMap_eq_kraus V σ din dout hr] at h
  have hemb := h.mul_mul_conjTranspose_same V
  simp only [Matrix.mul_sub, Matrix.sub_mul] at hemb
  rw [embedded_cartan_branch V k din dout hr σ] at hemb
  exact Matrix.le_iff.mpr hemb

/-- Retaining the selected environmental matrix element in the actual
reverse partial trace gives the reverse highest-weight branch. -/
theorem reverse_retained_branch_le (V : Matrix (A × B) C ℂ) (k : B)
    {τ : Matrix C C ℂ} (hτ : τ.PosSemidef) :
    (basisEmbedding (A := A) k).conjTranspose * V * τ * V.conjTranspose * basisEmbedding (A := A) k ≤
      reverseMap V τ := by
  apply Matrix.le_iff.mpr
  rw [reverseMap_eq_kraus]
  have h := krausMap_sub_branch_positive (reverseKraus V) k hτ
  simpa only [reverseKraus_eq_compression, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc] using h

end FreeEntropy.CartanChannel
