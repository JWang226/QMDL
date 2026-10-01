# Quantum minimum description of density matrices

Lean 4 formalization of Theorems 1 and 2 in the [Article](article.tex), by
Patrick Hayden, Alexander Maloney, Jinzhao Wang, and Yuxiang Yang.
Developed with assistance from Codex.

Both current manuscripts are included: the [Article](article.tex) gives the
proofs, and the [Letter](letter.tex) explains the physical free-entropy relation.
The Lean certificates cover the Article results listed below.

[Project wiki](https://jwang226.github.io/QMDL/) ·
[Proof structure](https://jwang226.github.io/QMDL/proof-structure/) ·
[Statement-to-Lean map](metadata/natural-language-map.json)

## Results and scope

| Result | Checked declaration | Conclusion |
| --- | --- | --- |
| Theorem 1: achievability | [FreeEntropy.theorem1_achievability](lean/FreeEntropy/Theorem1Complete.lean) | Actual CPTP codes with the exact additive memory constant and worst-case error $O(\log n/\sqrt n)$. |
| Theorem 1: converse | [FreeEntropy.theorem1_converse](lean/FreeEntropy/Theorem1Complete.lean) | Matching memory lower bound for arbitrary codes with vanishing Haar-average error; also covers vanishing worst-case error. |
| Theorem 2: cloning | [FreeEntropy.ExteriorRepresentation.theorem2_cloning_accuracy_choi](lean/FreeEntropy/Theorem2Choi.lean) | Both original Choi-projector channel bounds, including signed dominant differences, rank one, and equal rows. |

The dimension and spectrum are fixed, with distinct positive eigenvalues and
possible zeros. The cloning theorem assumes $d\ge2$, dominant natural rows
supported on the first $r$ coordinates, and a dominant integral difference.
Representation theory, dimensions, concentration, covariance, and
Choi/Petz identities are proved dependencies. The entire manuscript and its
broader extensions are not claimed to be formalized; see [exact scope](docs/FORMALIZATION_STATUS.md).

The proof library has no unresolved placeholders or custom axioms. Its audited
axioms are only `propext`, `Classical.choice`, and `Quot.sound`.
The deliberate holes in `lean/ComparatorChallenges/` are independent expected
statements, excluded from the proof library. Comparator checks their match to
the proved statements; its [imported-definition trust boundary](lean/ComparatorChallenges/trusted-boundary.json)
is explicit. These checks do not replace human review of correspondence with the paper.

**Recorded status:** a clean local Lean build and axiom audit, all three local
Comparator diagnostics, and all three independent Nanoda checks passed.
Independent human review and a Linux-sandboxed Comparator run remain pending.
[Evidence and reproduction details](docs/REPRODUCIBILITY.md) distinguish these
completed local checks from the configured [CI workflow](.github/workflows/lean.yml).

## Reproduce the Lean proof check

On macOS or Linux, install [elan](https://github.com/leanprover/elan),
Python 3.11+, Git, and native compiler/linker tools (Xcode Command Line Tools
on macOS; a C/C++ build toolchain on Linux). Allow several GB of memory and
disk space, plus internet access for the initial dependencies.

```sh
git clone https://github.com/JWang226/QMDL.git
cd QMDL
export PATH="$HOME/.elan/bin:$PATH"
(cd lean && lake exe cache get && bash check.sh)
```

This builds the proof library and reader entry points, audits transitive axioms,
and writes [verification/summary.json](lean/verification/summary.json).
The recorded audit covers 270 proof modules and 2,499 public declarations,
including 1,873 proved declarations. Lean is pinned to **4.29.0-rc6**;
[the manifest](lean/lake-manifest.json) pins every dependency, including mathlib
`f156f7abd91ac67adb22bf999e5a71ba22e22e41`. Keep it; do not run `lake update`.

## Reproduce Comparator and Nanoda checks

Run these from the repository root after the Lean build, on trusted local sources.
Both commands below are **unsandboxed** and exit nonzero on failure.

Comparator compares expected statements and referenced definitions, checks
solution axioms, then replays the exported proofs in Lean's kernel:

```sh
python3 lean/ComparatorConfig/check_local.py
```

Comparator is pinned to `a4f696825c583ed8a5b4060d9a0faa5b882d365b`.
For the separate Rust kernel, install [Rustup](https://rustup.rs/), then:

```sh
tool_dir="$(mktemp -d)"
git clone https://github.com/ammkrn/nanoda_lib.git "$tool_dir/nanoda"
git -C "$tool_dir/nanoda" checkout --detach 3a2407216ee84a75f9e1aead6803d0578be06ae7
rustup toolchain install 1.90.0 --profile minimal
CARGO_TARGET_DIR="$tool_dir/nanoda/target" \
  cargo +1.90.0 build --release --locked --manifest-path "$tool_dir/nanoda/Cargo.toml"
python3 lean/ComparatorConfig/check_nanoda.py \
  --nanoda-bin "$tool_dir/nanoda/target/release/nanoda_bin"
```

Nanoda 0.4.19 checks each solution's exported dependency closure with the same
three permitted axioms. The wrapper also requires every named theorem to be
present in the export; Nanoda independently rejects missing targets.
[Tool pins and results](lean/ComparatorConfig/nanoda-status.json) bind the
recorded check to the actual source and exports.

For sandboxed upstream Comparator, follow the [Linux/Landrun setup](lean/ComparatorChallenges/README.md#sandboxed-reproduction-on-linux),
then run `bash check_comparator.sh --nanoda` from `lean/` with the real
Nanoda binary on `PATH`. Full Landlock support and an unprivileged Linux
account are required; an unavailable sandbox causes failure.

## Further documentation

- [Lean library guide](lean/README.md) and [wiki proof map](https://jwang226.github.io/QMDL/proof-structure/): mathematical dependencies.
- [Reproducibility](docs/REPRODUCIBILITY.md): metadata validation, source-only exports, and CI.
- [Comparator challenges](lean/ComparatorChallenges/README.md): expected statements, exact tools, and sandbox limitations.
- [Formalization metadata](formalization.yaml), [AI provenance](docs/AI_PROVENANCE.md), and [release checklist](docs/RELEASE_CHECKLIST.md).
- [Citation](CITATION.cff): cite the commit used. [LICENSE](LICENSE) records the pending license decision; [NOTICE](NOTICE) preserves attribution.
