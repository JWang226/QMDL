# Comparator challenges

These files follow the [ten-proofs challenge format](https://github.com/openai/ten-proofs/tree/main/ComparatorChallenges)
and the [September 29 AGMAI release recommendations](https://agmai.org/general-sep29/).
They contain independently written expected statements, with intentional `sorry`
holes. They are **not proofs**, are not imported by `FreeEntropy` or `All`, and are
excluded from the proof library's no-holes audit. Comparator checks the solution's
proof, including its transitive axiom closure.

| Configuration | Expected declarations | Solution module |
| --- | --- | --- |
| `Theorem1Achievability.json` | `FreeEntropy.theorem1_achievability` | `FreeEntropy.Theorem1Complete` |
| `Theorem1Converse.json` | `FreeEntropy.theorem1_converse`, `FreeEntropy.theorem1_converse_of_uniform` | `FreeEntropy.Theorem1Complete` |
| `Theorem2Choi.json` | `FreeEntropy.ExteriorRepresentation.theorem2_cloning_accuracy_choi` | `FreeEntropy.Theorem2Choi` |

Theorem 1's expected interface independently restates the spectrum, genuine CPTP
channels, tensor-power density matrices, trace distance, Haar-average and worst-case
error, and the complete QMDL formula. Its sole project import is the construction of
normalized Haar measure. Theorem 2 independently restates the literal partial-trace
Choi contractions; its constructed representation, state, and projector definitions
are imported. This larger trust boundary is explicit in `trusted-boundary.json`.
Neither challenge is an alias of a target proposition.

## Exact tooling and scope

Lean is pinned to `v4.29.0-rc6`. The project pins
[Comparator's matching tag](https://github.com/leanprover/comparator/tree/v4.29.0-rc6)
at commit `a4f696825c583ed8a5b4060d9a0faa5b882d365b`, with its locked
Lean4Checker and lean4export dependencies. The matching version accepts exactly
`challenge_module`, `solution_module`, `theorem_names`, `permitted_axioms`, and
`enable_nanoda`. It has no `permittedConstants` field or declaration-renaming map:
the same qualified declaration name is looked up in both environments. Definitions
referenced by the expected type are compared recursively, not silently allowlisted.
The separate trust-boundary inventory is documentation, not an extra Comparator
configuration field.

Only `propext`, `Quot.sound`, and `Classical.choice` are permitted solution axioms.
The committed configurations set `enable_nanoda` to false for the baseline Lean
kernel replay. The explicit Nanoda modes below add an independent Rust checker.
The challenge holes do not permit `sorryAx` in the solution.

## Sandboxed reproduction on Linux

Run as an unprivileged user on Linux with full Landlock ABI 9 support (Linux 7.1
or newer) and real `landrun` on `PATH`; the script refuses macOS and root. Its
strict preflight deliberately omits `--best-effort` and fails before Comparator
if any capability requested by the pinned Landrun is unsupported. From `lean/`:

```bash
./check_comparator.sh
# Or one case:
./check_comparator.sh ComparatorChallenges/Theorem2Choi.json
# Also invoke real Nanoda inside the upstream sandbox:
./check_comparator.sh --nanoda
```

The script builds the pinned Comparator and lean4export, exposes the real exporter
on `PATH`, and calls the unmodified upstream `lake exe comparator` for each JSON.
It contains no sandbox bypass or fake Landrun implementation.
The `--nanoda` option requires `nanoda_bin` on `PATH` and generates temporary
copies of the JSON configurations with `enable_nanoda: true`; it does not edit
the committed configurations or alter the pinned upstream Comparator.

For a pinned Landrun source build (Go 1.24 or newer), outside this repository:

```bash
git clone https://github.com/Zouuup/landrun.git
cd landrun
git checkout 811cfff51ceaf3d9843708aa6d22e9b84ccac8b4
go build -o landrun cmd/landrun/main.go
export PATH="$PWD:$PATH"
```

Consult [Landrun's requirements](https://github.com/Zouuup/landrun/tree/811cfff51ceaf3d9843708aa6d22e9b84ccac8b4)
and [Comparator's current sandbox guidance](https://github.com/leanprover/comparator#usage).
The pinned historical Comparator uses Landrun's `--best-effort` flag; the preceding
strict probe verifies full support for the pinned Landrun feature set. Current upstream
guidance additionally restricts AF_UNIX when running untrusted solutions, for
example through an appropriate `systemd-run` unit. A build on a machine with no
working sandbox is not a sandboxed verification result. The optional Comparator CI
job is manually enabled on a capable runner; ordinary hosted Ubuntu support is not
assumed. Its configuration has not been executed on the development Mac.

## Local diagnostic on macOS or Linux

```bash
python3 ComparatorConfig/check_local.py
```

This separately named, **unsandboxed** diagnostic exports both environments, calls
the pinned Comparator's exact statement/constant comparison and axiom checker, and
replays the solution export with Lean4Checker in Lean's kernel. It never invokes
Landrun or Nanoda. Use it only for trusted local sources; it is not a substitute for
the sandboxed run above.

## Independent Nanoda replay on macOS or Linux

The pin in `ComparatorConfig/nanoda-toolchain.json` selects upstream
[Nanoda 0.4.19](https://github.com/ammkrn/nanoda_lib/tree/3a2407216ee84a75f9e1aead6803d0578be06ae7)
at commit `3a2407216ee84a75f9e1aead6803d0578be06ae7`, built with Rust 1.90.0 and its
committed Cargo lockfile. This is the upstream repository linked by the pinned
Comparator. With Git, Rustup, Python 3, the project Lean toolchain and a native
linker available, the following commands work from the repository root. On macOS
the linker is provided by Xcode Command Line Tools; on Linux use the platform's
C/C++ build toolchain.

```bash
nanoda_tools=$(mktemp -d)
git clone https://github.com/ammkrn/nanoda_lib.git "$nanoda_tools/nanoda"
git -C "$nanoda_tools/nanoda" checkout --detach 3a2407216ee84a75f9e1aead6803d0578be06ae7
rustup toolchain install 1.90.0 --profile minimal
CARGO_TARGET_DIR="$nanoda_tools/nanoda/target" \
  cargo +1.90.0 build --release --locked --manifest-path "$nanoda_tools/nanoda/Cargo.toml"
python3 lean/ComparatorConfig/check_nanoda.py \
  --nanoda-bin "$nanoda_tools/nanoda/target/release/nanoda_bin"
```

This checks all three configurations using actual solution exports, including the
Nat, String and quotient roots requested by the pinned Comparator's Nanoda mode.
Only the three standard axioms are allowed; an unpermitted axiom causes a hard
error. The checker is **unsandboxed** and performs independent kernel replay only;
run the local Comparator diagnostic as well for expected-statement comparison.
It makes no tracked changes unless `--report PATH` is supplied. To expose the same
binary to the Linux `--nanoda` mode, add its `target/release` directory to `PATH`.
This Nanoda release can report `Unable to print axioms` after successful checking
when no pretty-print destination is selected. It is a display warning; the
typechecker result and process exit code determine whether the check passed.

## Recorded status

All challenge templates compile, and all three local diagnostics **passed** on a
clean isolated build: exact exported statements and referenced constants matched,
the solution axiom closures were accepted, and Lean kernel replay succeeded.
`verification-status.json` binds these results to source and artifact hashes.

The real sandboxed Comparator run is **not run** on the development Mac: Landrun
requires a capable Linux host. The baseline Comparator run had Nanoda disabled;
the separate Nanoda run **passed all three configurations** with strict axiom
checking. Its source, compiler, binary, exports and input hashes are recorded in
`ComparatorConfig/nanoda-status.json`. Neither local check constitutes a sandboxed
Comparator pass.
