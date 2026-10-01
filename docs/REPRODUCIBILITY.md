# Reproducing the Lean verification

The proof project stays in `lean/`; `article.tex` and `free.bib` stay at the
repository root. Verification does not compile or modify the manuscript.

## Pinned environment

The checked toolchain is **Lean 4.29.0-rc6**, recorded in
[`lean-toolchain`](../lean/lean-toolchain). Mathlib is pinned to
`f156f7abd91ac67adb22bf999e5a71ba22e22e41`. The full dependency revisions are
recorded in [`lake-manifest.json`](../lean/lake-manifest.json); keep this file
when copying the project. Do not run `lake update` as part of reproduction.

Install [elan](https://github.com/leanprover/elan), Python 3.11 or newer, Git,
and native compiler/linker tools (Xcode Command Line Tools on macOS). The
toolchain is selected automatically from `lean/lean-toolchain`. Internet
access is needed for the initial toolchain, public Git dependencies, and
mathlib's public compiled cache. Project proof artifacts are rebuilt locally.

Clone the public repository first:

```sh
git clone https://github.com/JWang226/QMDL.git
cd QMDL
export PATH="$HOME/.elan/bin:$PATH"
```

Then, from the repository root (or an unpacked source archive):

```sh
python3 -m venv .venv-release
. .venv-release/bin/activate
python3 -m pip install -r scripts/requirements-release.txt
python3 scripts/validate_artifacts.py --allow-stale-audit
cd lean
lake --version
lake exe cache get
bash check.sh
cd ..
python3 scripts/validate_artifacts.py
```

`check.sh` generates the declaration audit, builds `All` (including
`FreeEntropy` and the reader entrypoints), asks Lean
for the actual kernel dependencies of the audited declarations, and checks
the output. Success allows only `propext`, `Classical.choice`, and
`Quot.sound`; proof placeholders and custom axioms fail the core audit.
The report is written to `lean/verification/summary.json`. Raw build and
axiom logs are written beside it. These are generated evidence, not proof
inputs.

The separate comparator challenge templates deliberately contain expected
proof holes. They are not imported by `FreeEntropy` and are not counted as
proved declarations in the core audit. Comparator checking is a separate
check with its own tool and sandbox requirements; see the
[challenge documentation](../lean/ComparatorChallenges/README.md).
A successful core audit does not by itself
claim a successful comparator run.

## Statement comparison and independent kernel

From the repository root after the Lean build, run:

```sh
python3 lean/ComparatorConfig/check_local.py
```

This invokes the pinned Comparator's exact statement/constant and axiom checks,
then Lean kernel replay, for each of the three challenge configurations.
For the separately implemented Nanoda kernel, follow the pinned Rust/source
build commands in the [root README](../README.md#reproduce-comparator-and-nanoda-checks),
then run `lean/ComparatorConfig/check_nanoda.py` with the resulting binary.
Both commands work on macOS and Linux and are explicitly unsandboxed.
Nanoda checks each exported solution's dependency closure with unpermitted
axioms treated as errors; it does not perform statement comparison itself.

The [Nanoda toolchain record](../lean/ComparatorConfig/nanoda-toolchain.json)
pins the checker source, Rust version and Cargo lockfile. Its
[execution record](../lean/ComparatorConfig/nanoda-status.json) binds the
actual checked exports, configuration and source bytes. Re-run locally to
check your checkout; a bundled report is historical evidence. Use
`--report /tmp/qmdl-nanoda-result.json` to retain a new portable report.
The optional report is written only after every requested case succeeds.
Use a fresh report path: a failed rerun does not overwrite an older report.

## Source-only export

Do not zip the working manuscript directory: it can contain correspondence,
notes, older drafts, TeX build products, and local package symlinks.
[`prepare_release.py`](../scripts/prepare_release.py) uses an explicit
allowlist and rejects selected symlinks. It never copies `.lake/`, `.git/`,
private notes, letters, or draft documents.

After a successful current audit and completion of the publication metadata:

```sh
python3 scripts/prepare_release.py --list
python3 scripts/prepare_release.py --output /tmp/free-entropy-source.tar.gz
```

The archive contains the manuscript, its bibliography and required local
class/style files, proof and verification scripts, pinned configuration,
named publication metadata, the workflow, and a current portable audit
summary. `RELEASE_MANIFEST.json` records a SHA-256 digest for every selected
file and records every locked dependency. Raw machine-specific logs are
excluded; CI uploads newly generated logs separately.

The exporter checks that the audit's proof fingerprint matches the selected
proof source bytes. A stale summary makes the default export fail. It also
checks the Lean/mathlib pins and the original manuscript SHA-256:

```text
09fc0a6bb205180cd820be94d843a1dc0d4342a543492e30dde54e367ae843a9
```

`--include-manuscript-pdf` adds the existing `article.pdf` without
regenerating it. The default package omits that PDF. The original
`quantumarticle.cls` and `utphys.bst` are included unchanged under their own
notices; the formalization's license does not override those notices.

The exporter checks file selection and verification fingerprints, not the
sufficiency of copyright permissions. A bundled pending `LICENSE` notice
remains pending. The publication record and outstanding metadata decisions
are in [`RELEASE_CHECKLIST.md`](RELEASE_CHECKLIST.md).

For a clean build before fresh verification exists, use a preparation copy:

```sh
python3 scripts/prepare_release.py --allow-unverified \
  --directory /tmp/free-entropy-source
cd /tmp/free-entropy-source/lean
lake exe cache get
bash check.sh
cd ..
python3 -m venv .venv-release
. .venv-release/bin/activate
python3 -m pip install -r scripts/requirements-release.txt
python3 scripts/validate_artifacts.py
python3 scripts/prepare_release.py --output /tmp/free-entropy-verified.tar.gz
```

The destination must not already exist. `--allow-unverified` deliberately
omits the old audit summary and marks the manifest accordingly.
It retains a historical clean-reproduction record only when that record's
proof fingerprint, manuscript hash, toolchain and dependency pins match the
selected sources. The manifest labels this as earlier source evidence,
not as a result of the new export or CI run. This preserves the linked
record through the CI preparation/build/re-export sequence. A stale record
is omitted in preparation mode; the default exporter rejects a stale record
or a missing record referenced by `formalization.yaml`. If sources change,
refresh the clean-reproduction evidence before making a verified release.
`--allow-incomplete-metadata` is also available for preparation only; it
lists missing publication files and must not be mistaken for a completed
release. Neither option publishes anything or initializes Git.

Archive ordering, permissions, ownership, and gzip/tar timestamps are
normalized. Identical selected bytes produce identical archive bytes with
the same Python/zlib implementation and `SOURCE_DATE_EPOCH` (default zero).

## Continuous integration

[`lean.yml`](../.github/workflows/lean.yml) checks an exported source copy on
Ubuntu 24.04, installs a versioned, checksum-verified elan bootstrap, fetches
the locked public dependencies, and runs the actual build and axiom audit.
It also compiles the separate expected-statement templates; their deliberate
proof holes are not imported into the production library. The same job then
runs the local Comparator/Lean replay diagnostic, builds the pinned Nanoda
with Rust 1.90.0 and `cargo --locked`, and checks all three solution exports.
These two checker steps are explicitly unsandboxed. The old copied Nanoda
report is removed before checking, so the uploaded success report must be
produced by that job's actual run. It creates a release archive only after
the checks succeed. GitHub actions
are pinned by commit. The workflow uploads reports and the source archive
as CI artifacts; it does not create a public release.

A separate, manually enabled dependent CI job downloads that source archive
and invokes the unmodified pinned upstream Comparator on Linux with real Landrun. Landrun
is built from commit `811cfff51ceaf3d9843708aa6d22e9b84ccac8b4`; the
Comparator, Lean4Checker and lean4export revisions are locked in the Lean
manifest. Enable `run_comparator` through `workflow_dispatch` and select a
capable x86_64 Linux runner using `comparator_runner` (the CI bootstrap is
pinned for that architecture). The strict preflight requires
all features of the pinned Landrun (Landlock ABI 9 or newer); a default
Ubuntu 24.04 runner may not provide them and will fail rather than silently
weaken the check. The job launches the checker as the runner's non-root
UID/GID in a systemd service that also denies AF_UNIX sockets and new
privileges. Its log and job status are separate from the kernel audit. The
historical Comparator's sandbox limitations are documented in the challenge
README. This hosted-runner setup has not been executed locally, and an
unselected or unsupported job is not a completed Comparator run.

This packaging follows the reproducibility and statement-recording goals
of [AGMAI](https://agmai.org/general-sep29/) and the repository organization
illustrated by [OpenAI's ten-proofs](https://github.com/openai/ten-proofs).
See [`FORMALIZATION_STATUS.md`](FORMALIZATION_STATUS.md) for the statement
mapping and [`AI_PROVENANCE.md`](AI_PROVENANCE.md) for provenance. Workflow
configuration is not evidence that a hosted CI run has already occurred.

## Completed clean source reproduction

The local clean reproduction completed on **2026-10-01 UTC** (2026-09-30
Pacific time) on macOS arm64. All 270 proof modules were compiled in an
exported source copy with no existing project proof artifacts and no package
directory symlinks. All twelve dependencies were real public Git checkouts
at the locked revisions; the official public mathlib cache was used.

The build and actual kernel audit passed for 1,873 proved declarations and
2,499 public declarations, with only the three permitted standard axioms.
`lake build All` and all eight artifact-validation checks also passed.
[`reproducibility.json`](../lean/verification/reproducibility.json) records
the actual platform, dependency pins, commands, source fingerprint, and
outcome without machine-specific paths. Its fingerprint must match the
sources before the exporter will include it. This completed local result
does not assert that hosted CI or the Linux-sandboxed Comparator has run.
