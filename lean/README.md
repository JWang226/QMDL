# Lean formalization of Theorems 1 and 2

To check every verification layer from the repository root, run
`bash scripts/verify.sh all`. See [the verification guide](../docs/verify.md)
for prerequisites, separate modes and expected verdicts, and the
[Lean explorer](https://jwang226.github.io/Quantum-Minimum-Description-Length/proof-explorer/) for searchable
compiled statements and direct dependencies.

The final statements concern actual finite complex matrices and completely
positive trace-preserving (CPTP) channels. The physical source is
`(U diag(x) U†)^{⊗n}` on the literal tensor-word space. The spectrum is fixed,
its positive eigenvalues are distinct, and the unknown unitary ranges over
`U(d)`. Zero eigenvalues are included. The manuscript `../article.tex` is
unchanged.

## Main theorems

- **Theorem 1, achievability:** `FreeEntropy.theorem1_achievability` in
  [`FreeEntropy/Theorem1Complete.lean`](FreeEntropy/Theorem1Complete.lean)
  constructs a sequence of actual encoders and decoders, independent of the
  unknown unitary. Their log memory dimension is the manuscript's QMDL
  expression plus `o(1)`, including its additive constant. Their actual
  worst-case trace-distance error is `O(log₂(n)/√n)` and tends to zero.
- **Theorem 1, converse:** `FreeEntropy.theorem1_converse` in the same file
  proves the exact extended-real `liminf` lower bound for arbitrary physical
  CPTP codes whose actual normalized-Haar average reconstruction error
  tends to zero. `theorem1_converse_of_uniform` gives the worst-case version.
  All dimensions and positive ranks are covered, including `d=1`.
- **Theorem 2:**
  `FreeEntropy.ExteriorRepresentation.theorem2_cloning_accuracy_choi` in
  [`FreeEntropy/Theorem2Choi.lean`](FreeEntropy/Theorem2Choi.lean)
  proves both channel errors are at most `C(d,x) D/(bμ+1)`, for every unknown
  unitary, using the manuscript's original normalized Choi-projector
  partial-trace formulas. The source and target are the actual constructed
  canonical representation states; both CPTP maps are constructed. The hypotheses are
  the manuscript's spectrum, supported dominant natural rows, and dominant
  integral difference. Negative entries in that difference are allowed.
  `D` is the exact row L1 norm and `bμ` the computed minimum supported
  adjacent gap. Rank one and coincident rows are included.
  [`Theorem2Canonical.lean`](FreeEntropy/Theorem2Canonical.lean) states the
  same bounds in Cartan form, and [`Theorem2Petz.lean`](FreeEntropy/Theorem2Petz.lean)
  uses the literal Petz recovery expression for the reverse map.
  `CanonicalCloningSelf.lean` proves the Cartan formulas reduce to identity
  channels when the rows coincide.

The explicit cloning constant is
`choose(d,2) + 3*N*q/(1-q)^(N+1)`, with `N=choose(r,2)` and the spectrum's
maximum adjacent ratio `q`. The source is expressed in a diagonal reference
basis; varying `U` gives the complete known-spectrum orbit.

These endpoints have no supplied representation, decomposition, dimension,
weight-counting, normalization, covariance, concentration, local-error, or
source-transfer premises. Earlier conditional reduction lemmas remain as
reusable intermediate results.

## How the remaining inputs were proved

1. **Actual representations and classification.** Exterior-power tensor
   spaces construct the canonical unitary irreducibles. Physical tensor
   powers decompose into genuine irreducible sectors. Ordered Lie words
   prove highest-weight existence, uniqueness, weight cones, and unitary
   equivalence, identifying each physical sector with its canonical model.
2. **Actual dimensions.** `CanonicalCharacterIdentity.lean` proves the
   Weyl character identity from the actual representation's Casimir
   equation, root-cone support, permutation symmetry, and highest line.
   `WeylDimensionExtraction.lean` extracts the dimension by finite
   polynomial coefficients. `CanonicalDimension.lean` identifies the
   resulting determinant with the proved GT cardinality and Weyl product,
   then derives the padded target's exact memory expansion.
3. **Actual cloning estimates.** Ordered lowering operators and explicit
   minor polynomials prove upper and shallow exact weight multiplicities.
   A highest-weight slice proves global multiplicity monotonicity.
   The complete tensor decomposition gives the required local Casimir
   gap and traced block estimates. `SignedAuxiliaryModel.lean` constructs
   the auxiliary representation for signed differences. All finite
   normalization, spectral-envelope, rank-support, and dimension-loss
   estimates are proved before the final trace-distance bound.
4. **Full covariance and physical states.** Physical tensor embeddings
   recover group intertwiners from their Lie generators. A scalar unitary
   factor accounts for determinant shifts and cancels in the channels.
   `CanonicalMonomialState.lean` identifies actual normalized polynomial
   states with the relative-weight formulas, including zero eigenvalues.
   `PhysicalOrbitChannels.lean` identifies these with actual physical
   source sectors.
5. **Physical concentration and compression.** Actual sector copy counts
   are bounded by word-type counts. Entropy estimates yield the actual
   atypical mass bound. `PhysicalCloningChannels.lean` constructs total
   channels using Cartan maps on typical sectors and explicit replacement
   channels elsewhere. `PhysicalCloningAccuracy.lean` proves their uniform
   forward and reverse approximation bounds.
6. **Converse and endpoints.** The actual cyclic weight count proves a
   uniform positive spectral gap. Irreducibility and normalized Haar
   integration give the finite memory bound. `PhysicalCanonicalConverse.lean`
   transfers arbitrary physical codes to this actual orbit.
   `PhysicalUniformError.lean` defines the real worst-case reconstruction
   error as a supremum and proves the claimed uniform rate.
7. **Original channel definitions.** Tensor–Hom adjunction proves actual
   multiplicity one of the auxiliary representation in the Choi carrier.
   `CanonicalChoi.lean` constructs its orthogonal projector, rank, highest
   vector and cyclic range, and proves the normalized projector is the
   forward channel's Choi matrix. `CanonicalReverseChoi.lean` and
   `ReverseChoiRepresentation.lean` identify the reverse projector with the
   dual component, whose dominant highest weight and cyclicity are proved.
   `ChoiContraction.lean` checks the exact transpose and partial-trace
   convention. `CanonicalPetz.lean` proves the unique Hilbert–Schmidt
   adjoint, maximally mixed reference identity and full matrix-square-root
   Petz formula. These links introduce no projector, multiplicity or
   recovery hypotheses.

The stronger pure-state results remain available in `RankOneEndpoints.lean`
and `OccupationTheorem2.lean`, including exact reconstruction by symmetric
subspace compression and exact reverse pure-state cloning.

## Reproduce the verification

The project pins Lean `v4.29.0-rc6` and mathlib commit
`f156f7abd91ac67adb22bf999e5a71ba22e22e41`.

```sh
cd lean
./check.sh
```

`check.sh` builds the project and checks the transitive kernel axioms of
every public theorem and definition found by `audit.py`. It uses Lean's own
axiom collector, sharing the visited dependency set so common proofs are
traversed once; the final theorem endpoints also receive individual
`#print axioms` checks. The only allowed
axioms are `propext`, `Classical.choice`, and `Quot.sound`. Proof placeholders
and project-specific axioms are rejected. The generated evidence is:

- `verification/build.txt`: complete build log;
- `verification/axioms.txt`: kernel dependency audit covering every listed declaration;
- `verification/summary.json`: verification status, declaration counts,
  toolchain, proof-source fingerprint, and manuscript checksum.

The counts and fingerprints in the summary are authoritative only for the
source tree whose fingerprint they record; rerun the check after edits.
