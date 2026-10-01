# Lean formalization and reproduction

The Lean development proves the two main statements of the current
[[Article]]: optimal known-spectrum memory (`thm:qmdl`) and finite cloning
accuracy (`thm:main`). [[proof-structure|The proof map]] explains the route
from actual representations and channels to those endpoints.

## What is checked

| Result | Formal statement | Scope |
| --- | --- | --- |
| [[results/achievability|Theorem 1, achievability]] | `FreeEntropy.theorem1_achievability` | Actual CPTP encoders and decoders, exact additive memory constant, uniform error $O(\log n/\sqrt n)$. |
| [[results/converse|Theorem 1, converse]] | `FreeEntropy.theorem1_converse` | The matching lower bound for arbitrary physical codes with vanishing Haar-average error. |
| Worst-case converse | `FreeEntropy.theorem1_converse_of_uniform` | Vanishing worst-case error implies the same lower bound. |
| [[results/cloning-fidelity|Theorem 2, original channels]] | `FreeEntropy.ExteriorRepresentation.theorem2_cloning_accuracy_choi` | Both normalized Choi-projector channel bounds, for supported rows and dominant signed difference. |

The constructed Cartan and Petz forms are also connected to the original
channels by proved identities. Theorem 1 includes $d=1$ and all positive
ranks; Theorem 2 is stated for $d\ge2$ and includes rank one and equal rows.
Positive eigenvalues are distinct and fixed in the asymptotic limit.

The final statements do not take representation existence, dimensions,
weight bounds, covariance, concentration or source-transfer estimates as
unproved premises. The library supplies these inputs. The precise statements
and their source labels are connected by
[the manuscript-to-Lean map](https://github.com/JWang226/QMDL/blob/main/metadata/natural-language-map.json).

## Verification evidence

The current source record covers **270 proof modules**, **1,873 proved
declarations**, and **2,499 public declarations audited**. The only allowed
axioms are Lean's `propext`, `Classical.choice` and `Quot.sound`.

| Check | Recorded local result | What it establishes |
| --- | --- | --- |
| Clean Lean build and axiom audit | Passed | The formal proofs elaborate and their actual transitive axioms are permitted. |
| Comparator and Lean export replay | All three configurations passed, unsandboxed | The expected statements and referenced definitions match the solution; exported proofs replay in Lean. |
| Nanoda 0.4.19 | All three configurations passed, unsandboxed | A separately implemented Rust kernel accepts the exported solution dependencies. |
| Linux-sandboxed Comparator | Not run in the published local record | Requires a capable Linux host and real Landrun. |
| Independent human review | Not established | Mechanical checking does not itself certify the interpretation of the manuscript. |

The three configurations cover achievability, both converse variants, and
Choi cloning. Comparator challenge files intentionally contain expected-statement
proof holes; these fixtures are separate from the proved library. The
[challenge guide](https://github.com/JWang226/QMDL/blob/main/lean/ComparatorChallenges/README.md)
records which definitions are independently restated and which are reused.

The local evidence is tied to source fingerprints, rather than to whichever
files happen to be present later. Consult the
[audit summary](https://github.com/JWang226/QMDL/blob/main/lean/verification/summary.json),
[Comparator record](https://github.com/JWang226/QMDL/blob/main/lean/ComparatorChallenges/verification-status.json)
and [Nanoda record](https://github.com/JWang226/QMDL/blob/main/lean/ComparatorConfig/nanoda-status.json).
Live hosted results are available from
[GitHub Actions](https://github.com/JWang226/QMDL/actions/workflows/lean.yml);
this page does not infer a completed hosted run from workflow configuration.

## Reproduce the checks

Use the [repository README](https://github.com/JWang226/QMDL#reproduce-the-lean-proof-check)
for the full installation and fresh-checkout commands. It pins the Lean
and dependency versions and gives separate instructions for Comparator,
Nanoda and the Linux sandbox. Once the prerequisites and public dependency
cache are installed, the central commands from the repository root are:

```sh
(cd lean && bash check.sh)
python3 lean/ComparatorConfig/check_local.py
python3 lean/ComparatorConfig/check_nanoda.py --nanoda-bin /path/to/nanoda_bin
```

The final path must refer to the real binary built with the README's pinned
Nanoda source and Rust version. All three commands fail with a nonzero exit
status when their checks fail. The latter two commands are local, unsandboxed
checks intended for a trusted checkout.

## Limits of the claim

This is not a formalization of the entire Article, Letter or Notes. In
particular, the later universal-coding overhead, block-entropy asymptotic,
unknown-spectrum discussion and broader free-entropy/programming claims
are outside the two-theorem certificate. General channel propositions are
not all established in their full paper-level generality. The proof also
uses some sufficient supporting bounds rather than the sharpest constants
in intermediate paper lemmas.

See the [formalization status](https://github.com/JWang226/QMDL/blob/main/docs/FORMALIZATION_STATUS.md)
for precise scope, [formalization.yaml](https://github.com/JWang226/QMDL/blob/main/formalization.yaml)
for machine-readable provenance, and
[the release checklist](https://github.com/JWang226/QMDL/blob/main/docs/RELEASE_CHECKLIST.md)
for outstanding review and licensing metadata.
