#!/usr/bin/env python3
# Copyright (c) 2026 Free Entropy formalization contributors.
# See LICENSE and NOTICE in the repository root for license and attribution.
"""Export the actual solution proofs and check them with real, unsandboxed Nanoda.

This is an independent-kernel check, not a substitute for statement comparison or
the Linux sandbox. The export roots and kernel options match pinned Comparator.
"""

import argparse
import datetime
import hashlib
import json
from pathlib import Path
import shutil
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parents[1]
PRIMITIVES = [
    "Nat.add", "Nat.sub", "Nat.mul", "Nat.pow", "Nat.gcd", "Nat.div",
    "Nat.mod", "Nat.beq", "Nat.ble", "Nat.land", "Nat.lor", "Nat.xor",
    "Nat.shiftLeft", "Nat.shiftRight", "String.ofList",
]
BUILTINS = ["Nat", "String", "String.mk", "Char", "Char.ofNat", "List"]
QUOTIENTS = ["Quot", "Quot.mk", "Quot.lift", "Quot.ind"]
DEFAULT_CONFIGS = [
    "ComparatorChallenges/Theorem1Achievability.json",
    "ComparatorChallenges/Theorem1Converse.json",
    "ComparatorChallenges/Theorem2Choi.json",
]


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def run(args, **kwargs):
    subprocess.run(args, cwd=ROOT, check=True, **kwargs)


def theorem_names(config):
    """Require an explicit, nonempty set of ordinary dotted theorem names."""
    names = config.get("theorem_names")
    if (not isinstance(names, list) or not names
            or any(not isinstance(name, str) or not name or name != name.strip()
                   or any(not part for part in name.split(".")) for name in names)
            or len(set(names)) != len(names)):
        raise ValueError("theorem_names must be nonempty, unique dotted names")
    return names


def kernel_options(names, axioms):
    return {
        "use_stdin": True,
        "permitted_axioms": axioms,
        "unpermitted_axiom_hard_error": True,
        "nat_extension": True,
        "string_extension": True,
        "print_success_message": True,
        # The pinned parser checks these names even without a pretty-printer
        # destination. No proof terms are rendered. Exporter exit status alone
        # is insufficient: its missing-constant panic can still exit zero.
        "pp_declars": names,
        "unknown_pp_declar_hard_error": True,
        "pp_to_stdout": False,
        "print_axioms": False,
    }


def require_exported_theorems(path, names):
    """Check root presence and declaration kind in the export, not just names
    echoed into a report. Nanoda independently checks presence and all terms.
    Only the name table is retained; expression bodies are streamed.
    """
    wanted = {tuple(name.split(".")): name for name in names}
    name_table = {0: ()}
    found = set()
    with path.open() as handle:
        for line in handle:
            record = json.loads(line)
            if "in" in record:
                if "str" in record:
                    part = record["str"]
                    suffix = part["str"]
                else:
                    part = record["num"]
                    # Numeric Lean name components are not string components.
                    suffix = part["i"]
                name_table[record["in"]] = name_table[part["pre"]] + (suffix,)
            if "thm" in record:
                name = name_table[record["thm"]["name"]]
                if name in wanted:
                    if name in found:
                        raise ValueError(f"Duplicate exported theorem: {wanted[name]}")
                    found.add(name)
    missing = [label for name, label in wanted.items() if name not in found]
    if missing:
        raise ValueError("Required targets are missing or not theorem declarations: "
                         + ", ".join(missing))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--nanoda-bin", default="nanoda_bin",
                        help="Real Nanoda binary built from nanoda-toolchain.json")
    parser.add_argument("--report", type=Path,
                        help="Write a portable success record only after all checks pass")
    parser.add_argument("configs", nargs="*", help="Comparator JSON configurations")
    args = parser.parse_args()
    binary_name = shutil.which(args.nanoda_bin)
    if binary_name is None:
        parser.error("Nanoda binary not found; build the pinned source and pass --nanoda-bin")
    binary = Path(binary_name).resolve()
    configs = args.configs or DEFAULT_CONFIGS
    pin_path = ROOT / "ComparatorConfig/nanoda-toolchain.json"
    pin = json.loads(pin_path.read_text())
    print("UNSANDBOXED Nanoda independent-kernel check; Landrun is not run.", flush=True)
    print("Run check_local.py or Linux Comparator as well for statement comparison.", flush=True)
    run(["lake", "build", "lean4export"])
    exporter = ROOT / ".lake/packages/lean4export/.lake/build/bin/lean4export"
    results = {}
    for config_name in configs:
        config_path = (ROOT / config_name).resolve()
        config = json.loads(config_path.read_text())
        names = theorem_names(config)
        relative_config = config_path.relative_to(ROOT).as_posix()
        axioms = config["permitted_axioms"]
        if set(axioms) != {"propext", "Quot.sound", "Classical.choice"}:
            parser.error("These checks require exactly the three recorded standard axioms")
        run(["lake", "build", config["solution_module"]])
        targets = BUILTINS + names + axioms + PRIMITIVES
        if "Quot.sound" in axioms:
            targets += QUOTIENTS
        with tempfile.TemporaryDirectory(prefix="free-entropy-nanoda-") as temp:
            temp_path = Path(temp)
            export_path = temp_path / "solution.export"
            kernel_config = temp_path / "nanoda.json"
            kernel_config.write_text(json.dumps(kernel_options(names, axioms), indent=2) + "\n")
            print(f"Exporting Nanoda roots: {config['solution_module']}", flush=True)
            with export_path.open("wb") as handle:
                run(["lake", "env", str(exporter), config["solution_module"],
                     "--", *targets], stdout=handle)
            require_exported_theorems(export_path, names)
            print(f"Checking {relative_config} with real Nanoda.", flush=True)
            with export_path.open("rb") as handle:
                run([str(binary), str(kernel_config)], stdin=handle)
            results[relative_config] = {
                "status": "passed",
                "theorem_names": names,
                "exported_theorems_present": True,
                "config_sha256": digest(config_path),
                "solution_export_sha256": digest(export_path),
                "export_bytes": export_path.stat().st_size,
            }
        print(f"NANODA PASSED (UNSANDBOXED): {relative_config}", flush=True)
    if args.report:
        report = {
            "schema_version": 1,
            "status": "passed",
            "mode": "unsandboxed_independent_kernel",
            "sandboxed_comparator": "not_run",
            "completed_at_utc": datetime.datetime.now(datetime.timezone.utc).isoformat(),
            "lean_toolchain": (ROOT / "lean-toolchain").read_text().strip(),
            "nanoda": pin,
            "nanoda_binary_sha256": digest(binary),
            "permitted_axioms": ["propext", "Quot.sound", "Classical.choice"],
            "unpermitted_axiom_hard_error": True,
            "unknown_pp_declar_hard_error": True,
            "proof_sources_sha256": hashlib.sha256(b"".join(
                path.name.encode() + b"\0" + path.read_bytes()
                for path in sorted((ROOT / "FreeEntropy").glob("*.lean"))
            )).hexdigest(),
            "artifact_sha256": {
                "ComparatorConfig/check_nanoda.py": digest(Path(__file__).resolve()),
                "ComparatorConfig/nanoda-toolchain.json": digest(pin_path),
                "lake-manifest.json": digest(ROOT / "lake-manifest.json"),
                "lean-toolchain": digest(ROOT / "lean-toolchain"),
            },
            "cases": results,
        }
        args.report.parent.mkdir(parents=True, exist_ok=True)
        args.report.write_text(json.dumps(report, indent=2) + "\n")


if __name__ == "__main__":
    main()
