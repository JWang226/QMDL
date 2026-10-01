# Quantum minimum description of density matrices

Project wiki: [Free Entropy & QMDL](https://jwang226.github.io/QMDL/).

Lean 4 certificates for Theorems 1 and 2 of the accompanying
[manuscript](article.tex), by Patrick Hayden, Alexander Maloney, Jinzhao Wang,
and Yuxiang Yang. The formalization was developed with assistance from Codex.
The manuscript is preserved without changes.

The release layout follows the explicit result index, Comparator challenges,
and metadata approach of [openai/ten-proofs](https://github.com/openai/ten-proofs)
and the artifact recommendations in
[Responsible Release of AI-Generated Mathematics](https://agmai.org/general-sep29/).
This repository records the status of each check separately. The clean Lean
build, axiom audit, all three unsandboxed local Comparator diagnostics, and
all three independent Nanoda checks passed.
Independent human review and a Linux-sandboxed Comparator run remain pending.

## Results

| Manuscript result | Lean certificate | Statement |
| --- | --- | --- |
| Theorem 1: achievability | [`FreeEntropy.theorem1_achievability`](lean/FreeEntropy/Theorem1Complete.lean) | Constructed CPTP compression, the exact additive memory constant, and uniform error `O(log n / sqrt n)`. |
| Theorem 1: converse | [`FreeEntropy.theorem1_converse`](lean/FreeEntropy/Theorem1Complete.lean) | The matching memory lower bound for every code with vanishing Haar-average error; the uniform-error corollary is included. |
| Theorem 2: cloning accuracy | [`FreeEntropy.ExteriorRepresentation.theorem2_cloning_accuracy_choi`](lean/FreeEntropy/Theorem2Choi.lean) | Both original normalized Choi-projector channel bounds, including signed dominant differences, rank one, and coincident rows. |

The scope is these two theorems under the manuscript's stated spectrum and
row hypotheses. The entire manuscript is not claimed to be formalized.
The supporting representation theory, dimensions, concentration bounds,
channel construction, covariance, and Choi/Petz identifications are proved
in the local library. No additional literature results are inserted as
project-specific axioms.

The main theorem proofs use only `propext`, `Classical.choice`, and
`Quot.sound`. There are no unresolved placeholders in the proof development.
Deliberate placeholders in `lean/ComparatorChallenges/` specify independent
comparison targets and are excluded from this proof-status count.

## Reproduce the Lean proof check

Prerequisites: [elan](https://github.com/leanprover/elan), Python 3.11 or newer,
Git, and native build tools (Xcode Command Line Tools on macOS, or a C/C++
compiler and linker on Linux). Use macOS or Linux with several GB of available memory and disk space.
Internet access is needed to fetch the pinned Lean toolchain and dependencies.
The first build compiles all 270 project proof modules; keep `lake-manifest.json`
and do not run `lake update`.

```sh
git clone https://github.com/JWang226/QMDL.git
cd QMDL
export PATH="$HOME/.elan/bin:$PATH"
cd lean
lake exe cache get
bash check.sh
cd ..
```

`check.sh` builds the library, audits the transitive kernel axioms of the
public declarations, checks the reader entry points, and refreshes
`lean/verification/summary.json`. Success means all 1,873 proved declarations
and 2,499 public declarations were audited, with only the permitted standard
axioms. The toolchain is **Lean 4.29.0-rc6**; exact dependency commits are in
[`lean/lake-manifest.json`](lean/lake-manifest.json).

To build the reader entry points separately, from the repository root:

```sh
(cd lean && lake build Theorem1 Theorem2 All)
```

From the repository root, check the release metadata and manuscript mappings:

```sh
python3 -m venv .venv
.venv/bin/python -m pip install -r scripts/requirements-release.txt
.venv/bin/python scripts/validate_artifacts.py
```

The validator uses pinned, checksum-verified upstream metadata schemas. A
fresh proof audit must match the current source bytes for this check to pass.

## Reproduce Comparator and Nanoda checks

These checks serve different purposes. Comparator compares the expected
statements and their referenced definitions with the actual proof targets.
Lean replays the exported proof terms. Nanoda checks the exported solution
with a separately implemented Rust kernel. None of these replaces human
review of the manuscript-to-formal-statement correspondence.

After the Lean build above, from the repository root, run all three
Comparator cases (achievability, both converse variants, and Choi cloning):

```sh
python3 lean/ComparatorConfig/check_local.py
```

The command uses the pinned upstream Comparator comparison and axiom checks,
then Lean kernel replay. It prints `LOCAL DIAGNOSTIC PASSED` for each case
and exits nonzero on failure. This local command is **unsandboxed** and is
intended for this trusted source checkout.

For Nanoda, also install [Rustup](https://rustup.rs/), then build the pinned
checker and run it on all three cases:

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

The Nanoda check also runs locally without a sandbox. It prints
`NANODA PASSED (UNSANDBOXED)` for each case after successful checking.
All three cases passed with Nanoda 0.4.19; exact tool pins and source-bound
results are in [nanoda-toolchain.json](lean/ComparatorConfig/nanoda-toolchain.json)
and [nanoda-status.json](lean/ComparatorConfig/nanoda-status.json).
This release of Nanoda can also emit an `Unable to print axioms` display
warning after checking; see the challenge documentation. Unpermitted
axioms remain hard errors.

To run the **unmodified upstream Comparator in its Linux sandbox**, including
Nanoda, put that same `nanoda_bin` on `PATH`, build the pinned Landrun following
the [sandbox setup instructions](lean/ComparatorChallenges/README.md), and run:

```sh
export PATH="$tool_dir/nanoda/target/release:$PATH"
(cd lean && bash check_comparator.sh --nanoda)
```

This requires an unprivileged Linux account with full Landlock ABI 9 support.
The script fails if the sandbox is unavailable. A local diagnostic pass does
not claim a Linux-sandboxed pass. The challenge documentation describes the
statement trust boundary and the additional systemd restrictions for untrusted
sources. All checks return a nonzero exit status on failure.

See [reproducibility](docs/REPRODUCIBILITY.md) for clean source exports and CI.
The [Lean reproducibility workflow](https://github.com/JWang226/QMDL/actions/workflows/lean.yml)
runs the Lean audit, local Comparator diagnostic, and independent Nanoda
check on pushes and pull requests, with separate logs for each.

## Artifact guide

- [`formalization.yaml`](formalization.yaml): community-format scope, provenance, review status, and main-result metadata.
- [`metadata/natural-language-map.json`](metadata/natural-language-map.json): manuscript labels and statements mapped to Lean declarations and definitions.
- [`docs/FORMALIZATION_STATUS.md`](docs/FORMALIZATION_STATUS.md): exact coverage, assumptions, and verification status.
- [`lean/README.md`](lean/README.md): mathematical structure of the proof development.
- [`docs/AI_PROVENANCE.md`](docs/AI_PROVENANCE.md): disclosed prompts, tools, methods, and unavailable provenance data.
- [`lean/verification/summary.json`](lean/verification/summary.json): source fingerprint and kernel-audit evidence.
- [`docs/RELEASE_CHECKLIST.md`](docs/RELEASE_CHECKLIST.md): verification and remaining publication metadata decisions.
- [`scripts/prepare_release.py`](scripts/prepare_release.py): creates a source directory or archive from an explicit public-file allowlist.

## Source and attribution

[`CITATION.cff`](CITATION.cff) identifies the formalization and its mathematical
source. The repository is [JWang226/QMDL](https://github.com/JWang226/QMDL);
cite the commit used for reproduction. A persistent scholarly identifier has
not been assigned. [`LICENSE`](LICENSE) records the pending license decision
and does not grant an open-source license;
[`NOTICE`](NOTICE) preserves prior-code and third-party attribution. The
manuscript and bundled TeX support files have their own rights and notices.

The working folder also contains other drafts and generated files. They are
outside the release allowlist. The release exporter omits local caches,
machine-specific paths, and unrelated drafts. No GitHub repository is created
or updated by the build or export commands.
