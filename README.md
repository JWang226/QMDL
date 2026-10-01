# Quantum minimum description of density matrices

Lean 4 proofs of Theorems 1 and 2 in the [Article](article.tex), by Patrick Hayden,
Alexander Maloney, Jinzhao Wang and Yuxiang Yang. Developed with assistance from
Codex. The current [Article](article.tex), [Letter](letter.tex), shared bibliography
and Letter figure are included unchanged.

[Proof website](https://jwang226.github.io/QMDL/) ·
[Proof route](https://jwang226.github.io/QMDL/proof-structure/) ·
[Lean explorer](https://jwang226.github.io/QMDL/proof-explorer/) ·
[Verification guide](https://jwang226.github.io/QMDL/verify/)

## The statements

| Result | Checked declaration | Conclusion |
| --- | --- | --- |
| Article Theorem 1: achievability | [theorem1_achievability](https://jwang226.github.io/QMDL/proof-explorer/#declaration=FreeEntropy.theorem1_achievability) | Constructed CPTP codes attain the exact additive memory constant and worst-case error $O(\log n/\sqrt n)$. |
| Article Theorem 1: converse | [theorem1_converse](https://jwang226.github.io/QMDL/proof-explorer/#declaration=FreeEntropy.theorem1_converse) | Matching lower bound for arbitrary physical codes with vanishing Haar-average error; also covers vanishing worst-case error. |
| Article Theorem 2: cloning | [theorem2_cloning_accuracy_choi](https://jwang226.github.io/QMDL/proof-explorer/#declaration=FreeEntropy.ExteriorRepresentation.theorem2_cloning_accuracy_choi) | Both original Choi-projector channel bounds, including signed dominant differences, rank one and equal rows. |

The dimension and spectrum are fixed, with distinct positive eigenvalues and
possible zeros. Theorem 1 covers all positive ranks, including `d=1`. The cloning
theorem requires `d≥2`, supported natural partitions and a dominant integral
difference. Representation theory, dimensions, concentration, covariance and
Choi/Petz identities are proved dependencies.

The explorer shows the exact elaborated Lean types and declaration references.
[Source files](lean/FreeEntropy/Theorem1Complete.lean),
[the cloning endpoint](lean/FreeEntropy/Theorem2Choi.lean) and the
[statement map](metadata/natural-language-map.json) locate the certificates.
The Letter's tube-volume geometry, entropy offsets and double-scaling bridge,
and broader repeated-positive-spectrum/programming claims, are outside these
certificates. See [precise scope](docs/FORMALIZATION_STATUS.md).

## How it was verified

- **Lean:** a clean local build and transitive axiom audit passed for 270 proof
  modules, 1,873 proved declarations and 2,499 public declarations. Only
  `propext`, `Classical.choice` and `Quot.sound` are permitted; the proof library
  has no unresolved placeholders or project-specific axioms.
- **Comparator:** three local diagnostics compared expected statements and
  referenced definitions, checked axioms and replayed the proofs through Lean's
  kernel. The independent [challenge files](lean/ComparatorChallenges/) contain
  deliberate specification holes and are excluded from the proof library.
- **Nanoda:** the separately implemented Rust kernel accepted all three solution
  exports, including their dependency closures and required theorem roots.

Comparator diagnostics and Nanoda checks were unsandboxed. Independent human
review and Linux-sandboxed Comparator execution are not established.
[Recorded evidence](docs/REPRODUCIBILITY.md) describes completed runs;
the commands below perform new checks. English names and explanations are
reading aids: the exact formal statements determine what was proved.

## Check it yourself

Use **macOS or Linux**, [elan](https://github.com/leanprover/elan), Git, Python
3.11+, native C/C++ compiler/linker tools, and [Rustup](https://rustup.rs/) for
Nanoda. Initial setup needs internet access and space for the dependencies.
The wrapper prepares the pinned checker tools and saves fresh logs per run.

```sh
git clone https://github.com/JWang226/QMDL.git
cd QMDL
bash scripts/verify.sh all
```

Success ends with **`VERIFICATION PASSED: all`**. The command returns nonzero
if any requested check fails. Logs and the new Nanoda report are saved in the
printed `.verify-work/run-*` directory; old bundled reports are not a new pass.
For individual layers, from the same repository root:

```sh
bash scripts/verify.sh lean        # build + transitive axiom audit
bash scripts/verify.sh comparator  # expected statements + Lean kernel replay
bash scripts/verify.sh nanoda      # pinned independent Rust kernel
```

The default build uses public dependency caches. Comparator/Lean and Nanoda
replay the exported endpoint dependency closures. Lean is pinned to
**4.29.0-rc6**; [the lockfile](lean/lake-manifest.json) pins every dependency.
Comparator is pinned to `a4f696825c583ed8a5b4060d9a0faa5b882d365b`; Nanoda to
`3a2407216ee84a75f9e1aead6803d0578be06ae7`, built with Rust **1.90.0**.
Keep the pins; do not run `lake update`.

[The verification guide](docs/verify.md) gives the modes, exact
success markers and the separate Linux/Landrun sandbox procedure.
Metadata validation checks evidence bindings; it does not execute the checkers.

## Read the proof

Start with [the proof route](https://jwang226.github.io/QMDL/proof-structure/),
then use [the explorer](https://jwang226.github.io/QMDL/proof-explorer/) to search
public declarations, inspect their exact types and follow dependencies in both
directions. [The mathematical wiki](https://jwang226.github.io/QMDL/wiki-index/)
explains the concepts and paper-level arguments.

To browse a local Git checkout:

```sh
python3 -m venv .venv-docs
.venv-docs/bin/python -m pip install -r requirements.txt
.venv-docs/bin/mkdocs serve
```

Open the local URL printed by MkDocs. See [catalog generation](docs/PROOF_EXPLORER.md)
for rebuilding the explorer data from the Lean environment.

[Formalization metadata](formalization.yaml) · [AI provenance](docs/AI_PROVENANCE.md) ·
[Citation](CITATION.cff) · [License status](LICENSE) · [Attribution](NOTICE).
Cite the commit checked. Independent human review and the pending license
choice are recorded in the [release checklist](docs/RELEASE_CHECKLIST.md).

The reading and verification layout follows the example of
[Anthropic's FLT repository](https://github.com/anthropics/fermats-last-theorem)
and its [proof explorer](https://tianyipeng.github.io/fermats-last-theorem/).
