# Check the proof yourself

The supplied proof can be checked on macOS or Linux. Run the commands below from
a fresh clone of [JWang226/QMDL](https://github.com/JWang226/QMDL). The wrapper
fetches the locked dependencies, checks the Lean proof, compares its final
statements with the expected statements, and replays the proofs in a separate
Rust kernel. It does not compile or change the manuscripts.

## Prerequisites

Install [elan](https://github.com/leanprover/elan), Python 3.11 or newer, Git,
[Rustup](https://rustup.rs/), and native compiler/linker tools. On macOS the
native tools come from Xcode Command Line Tools; on Linux use a C/C++ build
toolchain. Initial dependency and checker builds require internet access.

Lean is selected by `lean/lean-toolchain`; all Lean dependency revisions are
locked in `lean/lake-manifest.json`. Keep those files and do not run `lake update`.
The wrapper puts the usual elan and Cargo installation directories on `PATH`.
Rustup is needed for the default Nanoda source build, but not for `lean` or
`comparator` mode.

## Run every check

```bash
git clone https://github.com/JWang226/QMDL.git
cd QMDL
bash scripts/verify.sh
```

The default is `all`. Each invocation creates a new `.verify-work/run-*`
directory and prints its location. Logs are streamed to the terminal and saved
there. If any requested stage fails, the command exits nonzero and prints
`VERIFICATION FAILED` with the failing stage. It prints `VERIFICATION PASSED: all`
only after every requested stage succeeds. Argument or prerequisite failures
exit before a run directory is created.

The stages are:

| Stage | What it checks | Saved output |
| --- | --- | --- |
| `lean` | Fetch the public mathlib cache, build `All`, and audit the actual transitive axioms of the proof library. | `lean.log`, `lean-summary.json` |
| `comparator` | Compare the three expected-statement configurations with the solutions, check the solution axioms, and replay their exports in Lean's kernel. | `comparator.log` |
| `nanoda-build` | Build the unmodified pinned Nanoda source with Rust 1.90.0 and `cargo --locked`; verify the source, package, compiler and lockfile pins. | `nanoda-build.log`, `nanoda-source/` |
| `nanoda-controls` | Accept a valid proof and reject missing targets, non-theorem roots, forbidden axioms, proof holes, and an ill-typed proof. | `nanoda-controls.log` |
| `nanoda` | Check all three actual solution exports with Nanoda, requiring the named theorem roots and allowing only the three standard axioms. | `nanoda.log`, `nanoda-result.json` |

Both kernel checks allow only `propext`, `Classical.choice`, and `Quot.sound`.
The three configurations cover four final declarations: Theorem 1 achievability,
its Haar-average and uniform converses, and Theorem 2's original Choi-channel
bound. Deliberate holes in the expected-statement templates are not proofs and
are excluded from the audited production library.

The initial build uses mathlib's public compiled cache and rebuilds the project
proofs. Comparator/Lean and Nanoda subsequently replay the exported final proofs
and their dependencies. A successful run verifies those formal statements; it
does not replace review of their correspondence with the manuscripts. See
[[proof-structure]] and [[formalization]].

## Run one layer

```bash
bash scripts/verify.sh lean
bash scripts/verify.sh comparator
bash scripts/verify.sh nanoda
```

Each command runs only the named layer and its required preparation. The
Comparator and Nanoda helpers build the Lean modules they need; their individual
modes do not perform the complete library-wide axiom audit. They still require
elan, Python, Git, and the pinned Lean dependencies. Run `lean` first to fetch the
public cache and check the entire library.

For a previously built Nanoda binary, use an absolute path:

```bash
bash scripts/verify.sh all --nanoda-bin /absolute/path/to/nanoda_bin
```

This option is valid for `all` and `nanoda`. It skips the Rust/source build and
runs the same controls and proof checks. You are responsible for the binary's
provenance; the wrapper does not infer that it came from the pinned source.
The fresh Nanoda report records its SHA-256. The standard build uses source
commit `3a2407216ee84a75f9e1aead6803d0578be06ae7`, package version 0.4.19, and
the compiler and lockfile recorded in
[nanoda-toolchain.json](https://github.com/JWang226/QMDL/blob/main/lean/ComparatorConfig/nanoda-toolchain.json).

## Read the verdict

For the recorded source snapshot, the Lean log ends with
`PASS: 2499 declarations; no placeholders or custom axioms.` The Comparator log
has three `LOCAL DIAGNOSTIC PASSED:` lines. The Nanoda log has three
`NANODA PASSED (UNSANDBOXED):` lines. The wrapper's final success line means that
all stages selected for that invocation returned success.

Use the newly printed run directory and the command's exit status. Reports
already committed in the repository describe earlier runs; their presence does
not mean your run passed. A failed run never receives a success result from this
wrapper. `run-info.json` records the invocation, and `result.txt` records its
outcome. Preflight failures produce an error instead of those files.

## Separate sandboxed verification

The Comparator and Nanoda steps above are **unsandboxed** and are intended for
trusted local sources. No mode automatically invokes the Linux sandbox.

The separate
[Linux/Landrun procedure](https://github.com/JWang226/QMDL/blob/main/lean/ComparatorChallenges/README.md#sandboxed-reproduction-on-linux)
requires an unprivileged Linux account and the full features of the pinned
Landrun. Missing sandbox support is a failure, not a successful verification.
Local macOS checks do not establish a sandboxed Comparator result.

For individual helper commands, evidence history, metadata validation,
source-only archives and CI details, see
[Reproducibility](https://github.com/JWang226/QMDL/blob/main/docs/REPRODUCIBILITY.md).
