/-
Copyright (c) 2026 Free Entropy formalization contributors.
See LICENSE and NOTICE in the repository root for license and attribution.
-/
import Mathlib
import ComparatorChallenges.ChannelInterface
import ComparatorChallenges.ErrorScale
import ComparatorChallenges.Qmdl
import FreeEntropy.UnitaryHaar

/-!
Expected-statement interface for Theorem 1. The definitions below are independently
restated, with their original fully qualified names, so Comparator compares their
bodies with the solution environment. This file imports no compression, cloning,
representation decomposition, or asymptotic proof module. Probability Haar measure
is the sole project import; its exact definition and all dependencies are compared.
-/
noncomputable section
open Matrix MeasureTheory Filter
open scoped BigOperators Topology MatrixOrder ComplexOrder
set_option backward.isDefEq.respectTransparency false

namespace FreeEntropy
structure FixedSpectrum (d r : ℕ) where
  rank_pos : 0 < r
  rank_le : r ≤ d
  eigenvalue : ℕ → ℝ
  positive : ∀ i, i < r → 0 < eigenvalue i
  decreasing : ∀ i j, i < j → j < r → eigenvalue j < eigenvalue i
  zero_padded : ∀ i, r ≤ i → i < d → eigenvalue i = 0
  normalized : ∑ i ∈ Finset.range r, eigenvalue i = 1
end FreeEntropy


namespace FreeEntropy.OrbitMemory
variable {H M G : Type*} [Fintype H] [DecidableEq H]
  [Fintype M] [DecidableEq M] [Fintype G]
noncomputable def tr (A : Matrix H H ℂ) : ℝ := A.trace.re
end FreeEntropy.OrbitMemory

namespace FreeEntropy.TraceDistance
open FreeEntropy.OrbitMemory
variable {H M : Type*} [Fintype H] [DecidableEq H] [Fintype M] [DecidableEq M]
noncomputable def traceNorm (X : Matrix H H ℂ) : ℝ := tr (CFC.abs X)
noncomputable def traceDistance (A B : Matrix H H ℂ) : ℝ := traceNorm (A - B) / 2
end FreeEntropy.TraceDistance

namespace FreeEntropy.TensorPowers
variable {H K L : Type*} [Fintype H] [Fintype K] [Fintype L]
  [DecidableEq H] [DecidableEq K] [DecidableEq L]
def matrix (n : ℕ) (A : Matrix H K ℂ) : Matrix (Fin n → H) (Fin n → K) ℂ :=
  fun x y => ∏ t, A (x t) (y t)
end FreeEntropy.TensorPowers


namespace FreeEntropy.SchurWeyl
open Channels TraceDistance
variable {d r : ℕ}
def physicalSpectrum (s : FixedSpectrum d r) : Fin d → ℝ := fun j => s.eigenvalue j

def physicalDensity (s : FixedSpectrum d r) (U : Matrix.unitaryGroup (Fin d) ℂ) :
    Matrix (Fin d) (Fin d) ℂ :=
  (U : Matrix (Fin d) (Fin d) ℂ) * Matrix.diagonal (fun j => (physicalSpectrum s j : ℂ)) *
    (U : Matrix (Fin d) (Fin d) ℂ)ᴴ

def physicalSource (s : FixedSpectrum d r) (n : ℕ) (U : Matrix.unitaryGroup (Fin d) ℂ) :
    Matrix (Fin n → Fin d) (Fin n → Fin d) ℂ := TensorPowers.matrix n (physicalDensity s U)

def mixedAverageError (s : FixedSpectrum d r) (n : ℕ)
    {B : Type*} [Fintype B] [DecidableEq B]
    (E : MatrixChannel (Fin n → Fin d) B) (D : MatrixChannel B (Fin n → Fin d)) : ℝ :=
  ∫ U, traceDistance (D.toFun (E.toFun (physicalSource s n U)))
    (physicalSource s n U) ∂UnitaryHaar.probabilityHaar (Fin d)

variable {B : Type*} [Fintype B] [DecidableEq B]
def mixedWorstError (s : FixedSpectrum d r) (n : ℕ)
    (E : MatrixChannel (Fin n → Fin d) B) (D : MatrixChannel B (Fin n → Fin d)) : ℝ :=
  sSup (Set.range (fun U : Matrix.unitaryGroup (Fin d) ℂ =>
    traceDistance (D.toFun (E.toFun (physicalSource s n U))) (physicalSource s n U)))
end FreeEntropy.SchurWeyl
