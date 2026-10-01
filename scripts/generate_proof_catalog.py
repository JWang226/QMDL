#!/usr/bin/env python3
# Copyright (c) 2026 Free Entropy formalization contributors.
# See LICENSE and NOTICE in the repository root for license and attribution.
"""Generate deterministic proof-browser data from a matching compiled Lean build.

No dependencies are inferred from source text. Lean exports the actual compiled
types, values' constant references, structural references, and module metadata.
--check verifies the saved catalog's source bindings and internal consistency;
it neither reruns Lean nor certifies the proof. Use the separate audit for that.
"""
from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
import re
import shutil
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parents[1]
OUTPUT = ROOT / "docs/assets/lean-catalog.json"
INPUTS = [
    "scripts/export_proof_catalog.lean", "scripts/generate_proof_catalog.py",
    "lean/Audit.lean", "lean/FreeEntropy.lean", "lean/lean-toolchain",
    "lean/lake-manifest.json", "metadata/natural-language-map.json",
]
DEPENDENCY_POLICY = (
    "Direct edges are constant references in the compiled ConstantInfo type and "
    "value (including opaque values), plus inductive/constructor/recursor "
    "structural references. Self-edges are omitted. Project membership is determined "
    "by the defining Lean module, not by spelling. Compiler auxiliaries are not "
    "silently bypassed: every project reference resolves to declarations or "
    "auxiliary_declarations. The latter also includes source-defined structures, "
    "private helpers and instances outside the audit's public declaration list. "
    "Reverse references are limited to these indexed project declarations. Module "
    "imports are a separate relation, not proof dependencies."
)
STATEMENT_POLICY = (
    "statement is Lean's pretty-printing of the compiled ConstantInfo.type, "
    "including generalized parameters; it is not a verbatim source quotation. "
    "Ordinary notation may hide implicit arguments or show proof arguments as ⋯; "
    "universe parameters are retained separately. Source links point to the defining module "
    "and declaration range exported by Lean when available. A supplemental node "
    "without a range links to its module. This documentation export is not a new "
    "kernel check and does not replace the source-bound proof audit."
)


def fail(message):
    raise SystemExit(f"FAILED: {message}")


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def proof_sha(lean):
    return hashlib.sha256(b"".join(
        p.name.encode() + b"\0" + p.read_bytes()
        for p in sorted((lean / "FreeEntropy").glob("*.lean"))
    )).hexdigest()


def read_json(path):
    return json.loads(path.read_text())


def canonical_json(value):
    return json.dumps(value, ensure_ascii=False, sort_keys=True, separators=(",", ":"))


def payload_sha(catalog):
    payload = {k: v for k, v in catalog.items() if k != "catalog_sha256"}
    return hashlib.sha256(canonical_json(payload).encode()).hexdigest()


def audit_names():
    # This is the existing audit's explicit seed list, not dependency extraction.
    names = re.findall(r"^    `([^,\s]+),?$", (ROOT / "lean/Audit.lean").read_text(), re.M)
    if not names or len(names) != len(set(names)):
        fail("the generated audit declaration list is absent or duplicated")
    return set(names)


def summary(lean):
    path = lean / "verification/summary.json"
    if not path.is_file():
        fail(f"missing passing audit summary at {path}; run the proof audit first")
    result = read_json(path)
    if result.get("status") != "passed" or result.get("proof_sources_sha256") != proof_sha(lean):
        fail(f"audit summary is stale or not passing: {path}")
    if result.get("lean_toolchain") != (lean / "lean-toolchain").read_text().strip():
        fail(f"audit toolchain does not match {lean}")
    return result


def binding():
    report = summary(ROOT / "lean")
    return {
        "proof_sources_sha256": proof_sha(ROOT / "lean"),
        "lean_toolchain": (ROOT / "lean/lean-toolchain").read_text().strip(),
        "mathlib_revision": report["mathlib_revision"],
        "input_sha256": {p: sha(ROOT / p) for p in INPUTS},
    }


def landmarks():
    return [
        {"id": item["id"], "title": item["title"],
         "names": [d["declaration"] for d in item.get("lean", [])]}
        for item in read_json(ROOT / "metadata/natural-language-map.json")["entries"]
        if item.get("lean")
    ]


def make_catalog(raw):
    primary = audit_names()
    names = {n["name"] for n in raw["declarations"]}
    if len(names) != len(raw["declarations"]):
        fail("Lean exporter returned duplicate declarations")
    if primary - names:
        fail(f"public audit names missing from compiled environment: {sorted(primary - names)}")
    nodes = []
    for item in sorted(raw["declarations"], key=lambda n: n["name"]):
        name = item["name"]
        refs = {k: sorted(set(item[k + "_references"]) - {name})
                for k in ("type", "value", "structural")}
        all_refs = set().union(*map(set, refs.values()))
        loc = item["location"]
        node = {
            "name": name, "kind": item["kind"], "module": item["module"],
            "file": "lean/" + item["module"].replace(".", "/") + ".lean",
            "line": loc["line"] if loc else None,
            "statement": item["statement"],
            "level_parameters": item["level_parameters"],
            "dependencies": sorted(all_refs & names),
            "external_dependencies": sorted(all_refs - names),
        }
        # Parallel masks preserve origin without repeating long constant names.
        for field in ("dependencies", "external_dependencies"):
            node[field.removesuffix("ies") + "y_origins"] = [
                sum(bit for category, bit in [("type", 1), ("value", 2), ("structural", 4)]
                    if ref in refs[category]) for ref in node[field]
            ]
        if loc:
            node["source_range"] = loc
        nodes.append(node)
    modules = [
        {"name": m["name"], "file": "lean/" + m["name"].replace(".", "/") + ".lean",
         "imports": sorted(set(m["imports"]))}
        for m in sorted(raw["modules"], key=lambda m: m["name"])
        if m["name"] != "FreeEntropy"
    ]
    declarations = [n for n in nodes if n["name"] in primary]
    auxiliary = [n for n in nodes if n["name"] not in primary]
    catalog = {
        "version": 1, **binding(),
        "counts": {"declarations": len(declarations),
                   "proved": sum(n["kind"] == "theorem" for n in declarations),
                   "modules": len(modules), "supplemental_declarations": len(auxiliary)},
        "dependency_policy": DEPENDENCY_POLICY,
        "statement_policy": STATEMENT_POLICY,
        "dependency_origin_bits": {"type": 1, "value": 2, "structural": 4},
        "declarations": declarations, "auxiliary_declarations": auxiliary,
        "modules": modules, "landmarks": landmarks(),
    }
    catalog["catalog_sha256"] = payload_sha(catalog)
    return catalog


def validate(catalog):
    if catalog.get("version") != 1:
        fail("unsupported proof catalog version")
    if catalog.get("catalog_sha256") != payload_sha(catalog):
        fail("catalog payload checksum does not match (data changed or corrupted)")
    for key, value in binding().items():
        if catalog.get(key) != value:
            fail(f"catalog source binding is stale: {key}")
    if catalog.get("dependency_policy") != DEPENDENCY_POLICY or catalog.get("statement_policy") != STATEMENT_POLICY:
        fail("catalog extraction policy is stale")
    if catalog.get("dependency_origin_bits") != {"type": 1, "value": 2, "structural": 4}:
        fail("unknown dependency origin bitmask encoding")
    primary = catalog["declarations"]
    nodes = primary + catalog["auxiliary_declarations"]
    names = {n["name"] for n in nodes}
    if len(names) != len(nodes) or {n["name"] for n in primary} != audit_names():
        fail("catalog declaration inventory differs from the public audit")
    modules = {m["name"]: m for m in catalog["modules"]}
    actual_modules = {"FreeEntropy." + p.stem for p in (ROOT / "lean/FreeEntropy").glob("*.lean")}
    if set(modules) != actual_modules or len(modules) != len(catalog["modules"]):
        fail("catalog module inventory differs from current proof sources")
    for n in nodes:
        if n["module"] not in modules or n["file"] != modules[n["module"]]["file"]:
            fail(f"inconsistent source location for {n['name']}")
        path = ROOT / n["file"]
        line = n["line"]
        if not path.is_file() or (line is not None and not 1 <= line <= len(path.read_text().splitlines())):
            fail(f"invalid source line for {n['name']}")
        if not isinstance(n["statement"], str) or not n["statement"].strip():
            fail(f"missing compiled statement for {n['name']}")
        direct = set(n["dependencies"])
        external = set(n["external_dependencies"])
        if not direct <= names or external & names or n["name"] in direct:
            fail(f"invalid direct dependency partition for {n['name']}")
        for field in ("dependencies", "external_dependencies"):
            masks = n[field.removesuffix("ies") + "y_origins"]
            if len(masks) != len(n[field]) or any(type(m) is not int or not 1 <= m <= 7 for m in masks):
                fail(f"invalid dependency origins for {n['name']}")
            if n[field] != sorted(set(n[field])):
                fail(f"dependency references are not unique and sorted for {n['name']}")
    report = summary(ROOT / "lean")
    expected_counts = {
        "declarations": len(primary), "proved": sum(n["kind"] == "theorem" for n in primary),
        "modules": len(modules), "supplemental_declarations": len(nodes) - len(primary),
    }
    if catalog["counts"] != expected_counts or len(primary) != report["total_public_declarations_audited"] or expected_counts["proved"] != report["proved_declarations_audited"]:
        fail("catalog counts disagree with its inventory or the proof audit")
    if catalog["landmarks"] != landmarks():
        fail("catalog manuscript landmarks are stale")
    for item in catalog["landmarks"]:
        if not set(item["names"]) <= names:
            fail(f"unresolved manuscript landmark {item['id']}")


def main():
    global ROOT, OUTPUT
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check", action="store_true", help="check saved data without invoking Lean")
    parser.add_argument("--root", type=Path, default=ROOT, help="source checkout root")
    parser.add_argument("--build-dir", type=Path,
                        help="matching already-built Lean project directory (default: lean/)")
    parser.add_argument("--lake", default=shutil.which("lake") or str(Path.home() / ".elan/bin/lake"))
    args = parser.parse_args()
    ROOT = args.root.resolve()
    OUTPUT = ROOT / "docs/assets/lean-catalog.json"
    if args.check:
        if not OUTPUT.is_file():
            fail("catalog does not exist; generate it first")
        catalog = read_json(OUTPUT)
        validate(catalog)
        print(f"PASS: source-bound catalog, {catalog['counts']}; no Lean rebuild performed.")
        return
    build = (args.build_dir or ROOT / "lean").resolve()
    current = binding()
    compiled = summary(build)
    if compiled["proof_sources_sha256"] != current["proof_sources_sha256"]:
        fail("selected build has different proof sources")
    for file in ("lean-toolchain", "lake-manifest.json", "FreeEntropy.lean"):
        if sha(build / file) != sha(ROOT / "lean" / file):
            fail(f"selected build has a different {file}")
    if not (build / ".lake/build/lib/lean/FreeEntropy.olean").is_file():
        fail("FreeEntropy is not built; run lake build FreeEntropy in the selected build")
    with tempfile.TemporaryDirectory(prefix="qmdl-proof-catalog-") as temp:
        raw = Path(temp) / "compiled.json"
        subprocess.run([args.lake, "env", "lean", "--run",
                        str(ROOT / "scripts/export_proof_catalog.lean"), str(raw)], cwd=build, check=True)
        catalog = make_catalog(read_json(raw))
    validate(catalog)
    OUTPUT.parent.mkdir(parents=True, exist_ok=True)
    OUTPUT.write_text(canonical_json(catalog) + "\n")
    print(f"Wrote {OUTPUT}: {catalog['counts']}")


if __name__ == "__main__":
    main()
