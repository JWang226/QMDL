#!/usr/bin/env python3
# Copyright (c) 2026 Free Entropy formalization contributors.
# See LICENSE and NOTICE in the repository root for license and attribution.
"""Unsandboxed Comparator diagnostic; never report a secure Comparator pass."""

import json
from pathlib import Path
import subprocess
import sys
import tempfile

ROOT = Path(__file__).resolve().parents[1]
PRIMITIVES = [
    "Nat.add", "Nat.sub", "Nat.mul", "Nat.pow", "Nat.gcd", "Nat.div",
    "Nat.mod", "Nat.beq", "Nat.ble", "Nat.land", "Nat.lor", "Nat.xor",
    "Nat.shiftLeft", "Nat.shiftRight", "String.ofList",
]


def run(args, **kwargs):
    subprocess.run(args, cwd=ROOT, check=True, **kwargs)


def main():
    configs = sys.argv[1:] or [
        "ComparatorChallenges/Theorem1Achievability.json",
        "ComparatorChallenges/Theorem1Converse.json",
        "ComparatorChallenges/Theorem2Choi.json",
    ]
    print("UNSANDBOXED local diagnostic; Landrun is not run; Nanoda is disabled.", flush=True)
    run(["lake", "build", "comparator", "lean4export"])
    exporter = ROOT / ".lake/packages/lean4export/.lake/build/bin/lean4export"
    for config_name in configs:
        config_path = ROOT / config_name
        config = json.loads(config_path.read_text())
        if config["enable_nanoda"]:
            raise SystemExit("Local diagnostic does not support nanoda.")
        run(["lake", "build", config["challenge_module"], config["solution_module"]])
        targets = config["theorem_names"] + config["permitted_axioms"] + PRIMITIVES
        with tempfile.TemporaryDirectory(prefix="free-entropy-comparator-") as temp:
            exports = []
            for side in ["challenge", "solution"]:
                out = Path(temp) / f"{side}.export"
                print(f"Exporting {side}: {config[side + '_module']}", flush=True)
                with out.open("w") as handle:
                    run(["lake", "env", str(exporter), config[side + "_module"],
                         "--", *targets], stdout=handle)
                exports.append(str(out))
            run(["lake", "env", "lean", "--run", "ComparatorConfig/ReplayExports.lean",
                 str(config_path), *exports])
        print(f"LOCAL DIAGNOSTIC PASSED: {config_name}", flush=True)


if __name__ == "__main__":
    main()
