#!/usr/bin/env python3
# Copyright (c) 2026 Free Entropy formalization contributors.
# See LICENSE and NOTICE in the repository root for license and attribution.
"""Export an explicit, symlink-free allowlist; never archive the working tree."""
from __future__ import annotations

import argparse
import gzip
import hashlib
import io
import json
import os
from pathlib import Path
import re
import tarfile

MANUSCRIPT_SHA256 = "09fc0a6bb205180cd820be94d843a1dc0d4342a543492e30dde54e367ae843a9"
LEAN_TOOLCHAIN = "leanprover/lean4:v4.29.0-rc6"
MATHLIB_REVISION = "f156f7abd91ac67adb22bf999e5a71ba22e22e41"
PREFIX = "free-entropy-formalization"

# Every non-proof file is individually named. New files require an explicit
# review of this list; recursive copies of the manuscript directory are unsafe.
CORE_FILES = (
    "article.tex", "free.bib", "quantumarticle.cls", "utphys.bst",
    "lean/lakefile.toml", "lean/lake-manifest.json", "lean/lean-toolchain",
    "lean/FreeEntropy.lean", "lean/Audit.lean", "lean/audit.py", "lean/check.sh",
    "lean/Theorem1.lean", "lean/Theorem2.lean", "lean/All.lean",
    "lean/README.md", "lean/.gitignore",
)
PUBLICATION_FILES = (
    "README.md", "LICENSE", "NOTICE", "CITATION.cff", ".gitignore",
    "formalization.yaml", "metadata/natural-language-map.json", "metadata/schema-sources.json",
    "docs/AI_PROVENANCE.md", "docs/RELEASE_CHECKLIST.md",
    "docs/FORMALIZATION_STATUS.md", "docs/REPRODUCIBILITY.md",
    ".github/workflows/lean.yml", "scripts/prepare_release.py",
    "scripts/validate_artifacts.py", "scripts/requirements-release.txt",
)
OPTIONAL_FILES = (
    "lean/ComparatorChallenges.lean", "lean/ComparatorChallenges/README.md",
    "lean/check_comparator.sh", "lean/ComparatorConfig/check_local.py",
    "lean/ComparatorConfig/ReplayExports.lean",
    "lean/ComparatorConfig/check_nanoda.py", "lean/ComparatorConfig/nanoda-toolchain.json",
    "lean/ComparatorConfig/nanoda-status.json",
)
SOURCE_PATTERNS = (
    "lean/FreeEntropy/*.lean",
    "lean/ComparatorChallenges/*.lean",
    "lean/ComparatorChallenges/*.json",
)


def digest(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def read_regular(root: Path, name: str) -> bytes:
    """Reject symlinks in both the selected file and every parent component."""
    path = root
    for component in Path(name).parts:
        path = path / component
        if path.is_symlink():
            raise ValueError(f"Refusing symlink in release input: {name}")
    if not path.is_file():
        raise ValueError(f"Required regular file is missing: {name}")
    return path.read_bytes()


def collect(root: Path, args: argparse.Namespace) -> tuple[dict[str, bytes], dict]:
    names = set(CORE_FILES)
    missing = [name for name in PUBLICATION_FILES if not (root / name).exists()]
    if missing and not args.allow_incomplete_metadata:
        raise ValueError("Publication metadata is incomplete: " + ", ".join(missing))
    names.update(name for name in PUBLICATION_FILES if (root / name).exists())
    names.update(name for name in OPTIONAL_FILES if (root / name).exists())
    for pattern in SOURCE_PATTERNS:
        names.update(path.relative_to(root).as_posix() for path in root.glob(pattern))
    if args.include_manuscript_pdf:
        names.add("article.pdf")
    files = {name: read_regular(root, name) for name in sorted(names)}
    if digest(files["article.tex"]) != MANUSCRIPT_SHA256:
        raise ValueError("article.tex differs from the authorized original manuscript")
    if files["lean/lean-toolchain"].decode().strip() != LEAN_TOOLCHAIN:
        raise ValueError("Lean toolchain does not match the pinned release toolchain")
    lock = json.loads(files["lean/lake-manifest.json"])
    dependencies = {}
    for package in lock["packages"]:
        if (package["type"] != "git"
                or not re.fullmatch(r"[0-9a-f]{40}", package["rev"])
                or not package["url"].startswith("https://github.com/")):
            raise ValueError(f"Dependency is not a public, immutable Git pin: {package['name']}")
        dependencies[package["name"]] = {"url": package["url"], "revision": package["rev"]}
    if dependencies.get("mathlib", {}).get("revision") != MATHLIB_REVISION:
        raise ValueError("Mathlib lock does not match the authorized revision")
    mathlib_config = [section for section in files["lean/lakefile.toml"].decode().split("[[require]]")
                      if re.search(r'^name\s*=\s*"mathlib"\s*$', section, re.MULTILINE)]
    if len(mathlib_config) != 1 or not re.search(
            rf'^rev\s*=\s*"{MATHLIB_REVISION}"\s*$', mathlib_config[0], re.MULTILINE):
        raise ValueError("Mathlib package configuration is not pinned to the authorized revision")

    proof_names = sorted(name for name in files if name.startswith("lean/FreeEntropy/")
                         and name.endswith(".lean"))
    if not proof_names:
        raise ValueError("No proof modules selected")
    # Match audit.py's source fingerprint, including the file names and bytes.
    proof_hash = digest(b"".join(Path(name).name.encode() + b"\0" + files[name]
                                 for name in proof_names))
    expected = {
        "status": "passed", "proof_sources_sha256": proof_hash,
        "manuscript_sha256": MANUSCRIPT_SHA256,
        "lean_toolchain": LEAN_TOOLCHAIN, "mathlib_revision": MATHLIB_REVISION,
    }
    verification = "not bundled; run lean/check.sh"
    if not args.allow_unverified:
        summary_name = "lean/verification/summary.json"
        summary_bytes = read_regular(root, summary_name)
        summary = json.loads(summary_bytes)
        for key, value in expected.items():
            if summary.get(key) != value:
                raise ValueError(f"Verification summary is stale or unsuccessful: {key}")
        if re.search(rb"/(?:Users|home|private|var|tmp)/|[A-Za-z]:\\\\", summary_bytes):
            raise ValueError("Verification summary contains a machine-specific absolute path")
        files[summary_name] = summary_bytes
        verification = "current successful kernel audit summary bundled"
    # Preserve matching earlier evidence through preparation/CI copies, without
    # treating a copy operation as a new execution of the recorded checks.
    reproducibility_name = "lean/verification/reproducibility.json"
    historical_reproducibility = {
        "status": "not present",
        "role": "Historical source-matching evidence, not a result of this export or a new CI run",
    }
    if (root / reproducibility_name).exists():
        record_bytes = read_regular(root, reproducibility_name)
        record = json.loads(record_bytes)
        mismatches = [key for key, value in expected.items() if record.get(key) != value]
        if record.get("dependencies") != dependencies:
            mismatches.append("dependencies")
        if re.search(rb"/(?:Users|home|private|var|tmp)/|[A-Za-z]:\\\\", record_bytes):
            raise ValueError("Clean reproduction record contains a machine-specific absolute path")
        if mismatches:
            if not args.allow_unverified:
                raise ValueError("Clean reproduction record is stale or unsuccessful: " + ", ".join(mismatches))
            historical_reproducibility["status"] = "omitted stale record"
            historical_reproducibility["mismatched_fields"] = mismatches
        else:
            files[reproducibility_name] = record_bytes
            historical_reproducibility["status"] = "included matching record"
            historical_reproducibility["file"] = reproducibility_name
            historical_reproducibility["recorded_at_utc"] = record.get("checked_at_utc")
    if (not args.allow_unverified
            and reproducibility_name.encode() in files.get("formalization.yaml", b"")
            and reproducibility_name not in files):
        raise ValueError("formalization.yaml references a missing clean reproduction record")
    manifest = {
        "format_version": 1,
        "manuscript_sha256": MANUSCRIPT_SHA256,
        "lean_toolchain": LEAN_TOOLCHAIN,
        "dependencies": dependencies,
        "proof_sources_sha256": proof_hash,
        "verification": verification,
        "historical_reproducibility": historical_reproducibility,
        "missing_publication_metadata": missing,
        "files": {name: {"sha256": digest(data), "bytes": len(data)}
                  for name, data in sorted(files.items())},
    }
    files["RELEASE_MANIFEST.json"] = (json.dumps(manifest, indent=2, sort_keys=True) + "\n").encode()
    return files, manifest


def mode(name: str) -> int:
    return 0o755 if name.endswith((".sh", ".py")) else 0o644


def export_directory(destination: Path, files: dict[str, bytes]) -> None:
    if destination.exists():
        raise ValueError("Destination must not exist: " + str(destination))
    destination.mkdir(parents=True)
    for name, data in sorted(files.items()):
        path = destination / name
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_bytes(data)
        path.chmod(mode(name))


def export_archive(destination: Path, files: dict[str, bytes]) -> None:
    # Stable ordering, permissions, ownership and timestamps make equal inputs
    # produce equal bytes. SOURCE_DATE_EPOCH can deliberately override epoch 0.
    epoch = int(os.environ.get("SOURCE_DATE_EPOCH", "0"))
    if epoch < 0:
        raise ValueError("SOURCE_DATE_EPOCH must be nonnegative")
    destination.parent.mkdir(parents=True, exist_ok=True)
    with destination.open("xb") as output:
        with gzip.GzipFile(filename="", mode="wb", fileobj=output, mtime=epoch) as compressed:
            with tarfile.open(fileobj=compressed, mode="w", format=tarfile.PAX_FORMAT) as archive:
                for name, data in sorted(files.items()):
                    info = tarfile.TarInfo(f"{PREFIX}/{name}")
                    info.size, info.mode, info.mtime = len(data), mode(name), epoch
                    archive.addfile(info, io.BytesIO(data))


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", type=Path, default=Path(__file__).resolve().parents[1],
                        help="source root (default: parent of scripts/)")
    destinations = parser.add_mutually_exclusive_group(required=True)
    destinations.add_argument("--output", type=Path, help="create a new deterministic .tar.gz")
    destinations.add_argument("--directory", type=Path, help="create a new source-only directory")
    destinations.add_argument("--list", action="store_true", help="print the selected files")
    parser.add_argument("--include-manuscript-pdf", action="store_true",
                        help="also include the existing article.pdf, without regenerating it")
    parser.add_argument("--allow-unverified", action="store_true",
                        help="preparation only: omit verification summary before a fresh build")
    parser.add_argument("--allow-incomplete-metadata", action="store_true",
                        help="preparation only: permit missing publication metadata/license")
    args = parser.parse_args()
    root = args.root.resolve(strict=True)
    try:
        files, manifest = collect(root, args)
        if args.list:
            print("\n".join(sorted(files)))
        elif args.directory:
            export_directory(args.directory, files)
        else:
            export_archive(args.output, files)
        # Confirm the input remained intact throughout collection/export.
        if digest(read_regular(root, "article.tex")) != MANUSCRIPT_SHA256:
            raise ValueError("Manuscript changed during export")
        print(f"Selected {len(files)} files; manuscript SHA-256 {MANUSCRIPT_SHA256}.")
        print("Verification: " + manifest["verification"] + ".")
        print("Historical reproduction evidence: " + manifest["historical_reproducibility"]["status"] + ".")
        if manifest["missing_publication_metadata"]:
            print("PREPARATION ONLY: missing " + ", ".join(manifest["missing_publication_metadata"]))
    except (ValueError, OSError, KeyError, json.JSONDecodeError) as error:
        parser.exit(1, f"Export failed: {error}\n")


if __name__ == "__main__":
    main()
