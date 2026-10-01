#!/usr/bin/env python3
# Copyright (c) 2026 Free Entropy formalization contributors.
# See LICENSE and NOTICE in the repository root for license and attribution.
"""Validate release metadata and audit freshness without rebuilding Lean.

Install scripts/requirements-release.txt with Python 3.11+. Default mode requires
an existing passing audit summary matching the current proof source. Preparation
mode (--allow-stale-audit) permits missing/stale evidence, never a proof-pass claim.
Pinned official schemas are fetched over HTTPS and digest-checked. --schema-cache
may point to an external cache; each cached schema is still digest-checked.
This validates artifacts; it does not run Comparator or Nanoda or authorize publication.
"""
from __future__ import annotations

import argparse
from collections import Counter
import datetime
import hashlib
import json
from pathlib import Path, PurePosixPath
import re
import subprocess
import sys
import tomllib
from urllib.request import urlopen

try:
    import jsonschema
    import yaml
except ImportError as exc:
    raise SystemExit("Install scripts/requirements-release.txt before validation") from exc

ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
TOOLCHAIN = "leanprover/lean4:v4.29.0-rc6"
MATHLIB_REVISION = "f156f7abd91ac67adb22bf999e5a71ba22e22e41"
COMPARATOR_REVISION = "a4f696825c583ed8a5b4060d9a0faa5b882d365b"
NANODA_PIN = {
    "repository": "https://github.com/ammkrn/nanoda_lib.git",
    "commit": "3a2407216ee84a75f9e1aead6803d0578be06ae7",
    "package_version": "0.4.19",
    "rust_toolchain": "1.90.0",
    "rust_commit": "1159e78c4747b02ef996e55082b704c09b970588",
    "cargo_lock_sha256": "9b921e794ce5ed515eb31db9ada0c2f34df999b6c9b5135ad308a412872e42be",
    "build_command": "cargo +1.90.0 build --release --locked",
    "binary": "target/release/nanoda_bin",
}
COPYRIGHT = "Copyright (c) 2026 Free Entropy formalization contributors."
NOTICE = "See LICENSE and NOTICE in the repository root for license and attribution."
SCHEMAS = {
    "formalization-v0.3": (
        "https://raw.githubusercontent.com/mathlib-initiative/formalization.yaml/"
        "99c678e569c7c4c0772db297c5ddd5e4c9b6322e/schema/v0.3.schema.json",
        "93247a8093ea0bb622650e8f387bcc95c4e4c7941408974d6779341844262b27",
        "formalization.yaml",
    ),
    "citation-file-format-1.2.0": (
        "https://raw.githubusercontent.com/citation-file-format/citation-file-format/"
        "396f738fb025b1d8acdb02a56ffc923f95dc8999/schema.json",
        "0b8d22140da702d766df318dcff3a91af2f39521298dcf36d76315fd99cc169b",
        "CITATION.cff",
    ),
}
CONFIG_NAMES = ("Theorem1Achievability", "Theorem1Converse", "Theorem2Choi")
CONFIG_KEYS = {"challenge_module", "solution_module", "theorem_names", "permitted_axioms", "enable_nanoda"}
MODULE_RE = r"[A-Za-z_][A-Za-z_0-9]*(?:\.[A-Za-z_][A-Za-z_0-9]*)*"
CONFIG_SCHEMA = {
    "type": "object", "additionalProperties": False, "required": sorted(CONFIG_KEYS),
    "properties": {
        "challenge_module": {"type": "string", "pattern": "^ComparatorChallenges\\." + MODULE_RE + "$"},
        "solution_module": {"type": "string", "pattern": "^FreeEntropy\\." + MODULE_RE + "$"},
        "theorem_names": {"type": "array", "minItems": 1, "uniqueItems": True,
                          "items": {"type": "string", "pattern": "^" + MODULE_RE + "$"}},
        "permitted_axioms": {"type": "array", "uniqueItems": True,
                             "items": {"enum": sorted(ALLOWED_AXIOMS)}},
        "enable_nanoda": {"type": "boolean"},
    },
}


def digest(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def unique_pairs(pairs):
    result = {}
    for key, value in pairs:
        if key in result:
            raise ValueError(f"Duplicate object key: {key!r}")
        result[key] = value
    return result


class UniqueLoader(yaml.SafeLoader):
    pass


def yaml_mapping(loader, node, deep=False):
    return unique_pairs((loader.construct_object(k, deep=deep), loader.construct_object(v, deep=deep))
                        for k, v in node.value)


UniqueLoader.add_constructor(yaml.resolver.BaseResolver.DEFAULT_MAPPING_TAG, yaml_mapping)


def strip_lean_noise(source: str) -> str:
    """Blank nested comments and strings, preserving line/column offsets."""
    output, i, depth, quoted = [], 0, 0, False
    while i < len(source):
        c = source[i]
        if depth:
            if source.startswith("/-", i):
                output.extend("  "); depth += 1; i += 2
            elif source.startswith("-/", i):
                output.extend("  "); depth -= 1; i += 2
            else:
                output.append("\n" if c == "\n" else " "); i += 1
        elif quoted:
            if c == "\\" and i + 1 < len(source):
                output.extend("\n" if x == "\n" else " " for x in source[i:i+2]); i += 2
            else:
                output.append("\n" if c == "\n" else " "); quoted = c != '"'; i += 1
        elif source.startswith("/-", i):
            output.extend("  "); depth = 1; i += 2
        elif source.startswith("--", i):
            j = source.find("\n", i)
            j = len(source) if j == -1 else j
            output.extend(" " * (j-i)); i = j
        elif c == '"':
            output.append(" "); quoted = True; i += 1
        else:
            output.append(c); i += 1
    if depth or quoted:
        raise ValueError("Unterminated Lean comment or string")
    return "".join(output)


def lean_declarations(source: str) -> dict[str, tuple[str, int]]:
    """Locator index only: actual declaration/proof checking belongs to Lean."""
    scopes, result = [], {}
    for number, line in enumerate(strip_lean_noise(source).splitlines(), 1):
        scope = re.match(r"\s*(namespace|(?:noncomputable\s+)?section)\s*(\S*)", line)
        if scope:
            scopes.append((scope[1] == "namespace", scope[2])); continue
        if re.match(r"\s*end(?:\s|$)", line):
            if scopes:
                scopes.pop()
            continue
        decl = re.match(
            r"\s*(?:@\[[^\]]*\]\s*)?(?:noncomputable\s+)?"
            r"(theorem|lemma|def|abbrev|structure|inductive|class)\s+([^\s(:{]+)", line)
        if decl:
            prefix = ".".join(name for is_namespace, name in scopes if is_namespace)
            name = f"{prefix}.{decl[2]}" if prefix else decl[2]
            if name in result:
                raise ValueError(f"Duplicate declaration locator {name}")
            result[name] = (decl[1], number)
    return result


def imports(source: str) -> list[str]:
    found = []
    for line in strip_lean_noise(source).splitlines():
        m = re.match(r"\s*(?:(?:public|private)\s+)?import\s+(.+)", line)
        if m:
            found.extend(m[1].split())
    return found


class Validator:
    def __init__(self, root: Path, allow_stale: bool, schema_cache: Path | None):
        self.root, self.allow_stale, self.schema_cache = root, allow_stale, schema_cache
        self.errors, self.warnings, self.completed = [], [], []
        self.source, self.decls, self.configs = {}, {}, {}
        self.import_cache = {}
        self.audit_current = False

    def require(self, condition, message):
        if not condition:
            raise ValueError(message)

    def path(self, name: str) -> Path:
        self.require(isinstance(name, str) and name, "Empty/non-string artifact path")
        p = PurePosixPath(name)
        self.require(not p.is_absolute() and ".." not in p.parts and "\\" not in name,
                     f"Not a repository-relative path: {name}")
        path = self.root
        for part in p.parts:
            path = path / part
            self.require(not path.is_symlink(), f"Symlink is not an artifact source: {name}")
        self.require(path.is_file(), f"Missing file: {name}")
        return path

    def text(self, name):
        return self.path(name).read_text(encoding="utf-8")

    def read_json(self, name):
        return json.loads(self.text(name), object_pairs_hook=unique_pairs)

    def read_yaml(self, name):
        return yaml.load(self.text(name), Loader=UniqueLoader)

    def check(self, label, action):
        try:
            action()
            self.completed.append(label)
        except Exception as exc:
            self.errors.append(f"{label}: {exc}")

    def schema(self, name, record):
        url, expected, target = SCHEMAS[name]
        self.require((record.get("url"), record.get("sha256"), record.get("target")) ==
                     (url, expected, target), f"Schema registry differs from pinned {name}")
        self.require(record.get("revision") in url and record.get("path") in url,
                     f"Incorrect schema revision/path: {name}")
        cached = self.schema_cache / (name + ".schema.json") if self.schema_cache else None
        if cached and cached.exists():
            data = cached.read_bytes()
        else:
            with urlopen(url, timeout=30) as response:
                data = response.read(2_000_001)
            self.require(len(data) <= 2_000_000, "Schema response is unexpectedly large")
        self.require(digest(data) == expected, f"Schema digest mismatch: {name}")
        if cached and not cached.exists():
            cached.parent.mkdir(parents=True, exist_ok=True)
            cached.write_bytes(data)
        schema = json.loads(data, object_pairs_hook=unique_pairs)
        # The two pinned schemas use only internal references. Never follow an
        # unpinned external schema reference as part of the validation.
        def refs(value):
            if isinstance(value, dict):
                if "$ref" in value:
                    self.require(value["$ref"].startswith("#"), "Unpinned external schema reference")
                for v in value.values(): refs(v)
            elif isinstance(value, list):
                for v in value: refs(v)
        refs(schema)
        jsonschema.Draft7Validator.check_schema(schema)
        validator = jsonschema.Draft7Validator(schema, format_checker=jsonschema.FormatChecker())
        problems = list(validator.iter_errors(self.read_yaml(target)))
        self.require(not problems, "; ".join(
            f"{target}:{'/'.join(map(str, p.absolute_path))}: {p.message}" for p in problems[:8]))

    def schemas(self):
        registry = self.read_json("metadata/schema-sources.json")
        records = registry["sources"]
        self.require(len(records) == len(SCHEMAS), "Unexpected schema registry size")
        self.require({r["id"] for r in records} == set(SCHEMAS), "Unexpected schema registry entries")
        for record in records:
            self.schema(record["id"], record)
        self.require(self.read_yaml("formalization.yaml")["version"] == "v0.3", "Wrong metadata version")
        self.require(self.read_yaml("CITATION.cff")["cff-version"] == "1.2.0", "Wrong CFF version")

    def load_sources(self):
        files = sorted((self.root / "lean/FreeEntropy").glob("*.lean"))
        self.require(files, "No proof modules found")
        files += sorted((self.root / "lean").glob("*.lean"))
        files += sorted((self.root / "lean/ComparatorChallenges").rglob("*.lean"))
        for p in files:
            name = p.relative_to(self.root).as_posix()
            source = self.text(name)
            self.source[name] = source
            self.decls[name] = lean_declarations(source)

    def module_file(self, module):
        self.require(isinstance(module, str) and re.fullmatch(MODULE_RE, module), f"Invalid module: {module}")
        name = "lean/" + module.replace(".", "/") + ".lean"
        self.path(name)
        return name

    def declared(self, name, file, line=None):
        self.path(file)
        self.require(file in self.decls and name in self.decls[file],
                     f"Declaration {name} not found in {file}")
        if line is not None:
            self.require(type(line) is int and line > 0 and self.decls[file][name][1] == line,
                         f"Stale line locator: {file}:{line} for {name}; actual {self.decls[file][name][1]}")

    def source_imports(self, file):
        if file not in self.import_cache:
            self.import_cache[file] = imports(self.source[file])
        return self.import_cache[file]

    def import_closure(self, module):
        seen, todo = set(), [module]
        while todo:
            item = todo.pop()
            if item in seen: continue
            seen.add(item)
            if item.startswith(("FreeEntropy", "ComparatorChallenges")):
                name = self.module_file(item)
                todo.extend(self.source_imports(name))
        return seen

    def boundaries(self):
        for file, source in self.source.items():
            if "/ComparatorChallenges/" in file: continue
            for module in self.source_imports(file):
                self.require(not module.startswith("ComparatorChallenges"),
                             f"Production source imports challenge: {file} -> {module}")
                if module.split(".")[0] not in {"Mathlib", "Lean", "Std"}:
                    # Production imports must be another included local module,
                    # or the explicitly pinned Lean/Mathlib foundations.
                    self.module_file(module)
            if file.startswith("lean/FreeEntropy/"):
                self.require(not re.search(r"\b(?:sorry|admit|axiom)\b", strip_lean_noise(source)),
                             f"Proof placeholder or custom axiom in {file}")
        self.require("FreeEntropy.Theorem1Complete" in self.import_closure("FreeEntropy"),
                     "Root proof library does not import Theorem1Complete")
        self.require("FreeEntropy.Theorem2Choi" in self.import_closure("FreeEntropy"),
                     "Root proof library does not import Theorem2Choi")

    def headers(self):
        paths = set(self.source)
        for folder in ("scripts", "lean/ComparatorConfig"):
            for p in (self.root / folder).glob("*"):
                if p.suffix in {".py", ".sh", ".lean"}:
                    paths.add(p.relative_to(self.root).as_posix())
        paths.update(p.relative_to(self.root).as_posix() for p in (self.root / "lean").glob("*.sh"))
        paths.add("lean/audit.py")
        paths.add("scripts/requirements-release.txt")
        missing = [p for p in sorted(paths) if not all(
            marker in "\n".join(self.text(p).splitlines()[:10]) for marker in (COPYRIGHT, NOTICE))]
        self.require(not missing, "Missing copyright/NOTICE header: " + ", ".join(missing))

    def comparator(self):
        for name in CONFIG_NAMES:
            file = f"lean/ComparatorChallenges/{name}.json"
            config = self.read_json(file)
            jsonschema.Draft7Validator(CONFIG_SCHEMA).validate(config)
            self.require(set(config["permitted_axioms"]) == ALLOWED_AXIOMS, f"Wrong allowed axioms in {file}")
            challenge = self.module_file(config["challenge_module"])
            solution = self.module_file(config["solution_module"])
            self.require(config["solution_module"] not in self.import_closure(config["challenge_module"]),
                         f"Challenge transitively imports its solution module: {file}")
            for theorem in config["theorem_names"]:
                self.declared(theorem, challenge); self.declared(theorem, solution)
                self.require(self.decls[challenge][theorem][0] in {"theorem", "lemma"} and
                             self.decls[solution][theorem][0] in {"theorem", "lemma"},
                             f"Configured result is not a theorem: {theorem}")
            self.configs[file] = config
        # Metadata companions are not upstream runner configurations.
        boundary = self.read_json("lean/ComparatorChallenges/trusted-boundary.json")
        status = self.read_json("lean/ComparatorChallenges/verification-status.json")
        self.require(boundary["upstream_config_schema"]["commit"] == COMPARATOR_REVISION,
                     "Trusted-boundary Comparator pin differs")
        self.require(set(boundary["upstream_config_schema"]["keys"]) == CONFIG_KEYS,
                     "Trusted-boundary runner keys differ")
        self.require(status["comparator_commit"] == COMPARATOR_REVISION and
                     status["lean_toolchain"] == TOOLCHAIN, "Comparator status pins differ")
        self.comparator_evidence(status)
        if status.get("sandboxed_comparator") != "passed":
            self.warnings.append("Sandboxed Comparator execution is not recorded as passed; static config validation is not a run.")

    def proof_fingerprint(self):
        files = sorted((self.root / "lean/FreeEntropy").glob("*.lean"))
        return digest(b"".join(p.name.encode() + b"\0" + p.read_bytes() for p in files))

    def comparator_evidence(self, status):
        """Bindings establish report freshness, never promote pending checks to passed."""
        proof_hash = status.get("proof_sources_sha256")
        artifacts = status.get("artifact_sha256")
        if proof_hash is None and artifacts is None:
            completed = any(status.get(key) == "passed" for key in
                            ("challenge_elaboration", "sandboxed_comparator", "unsandboxed_local_diagnostic"))
            self.require(not completed, "Completed Comparator report has no source/artifact bindings")
            self.warnings.append("Comparator status has no freshness bindings; no completed run is established.")
            return
        self.require(isinstance(proof_hash, str) and re.fullmatch(r"[0-9a-f]{64}", proof_hash),
                     "Malformed Comparator proof-source hash")
        self.require(isinstance(artifacts, dict) and artifacts, "Malformed Comparator artifact hash map")
        required = {"ComparatorChallenges/PhysicalInterface.lean", "ComparatorChallenges/trusted-boundary.json",
                    "ComparatorConfig/ReplayExports.lean", "ComparatorConfig/check_local.py",
                    "lakefile.toml", "lake-manifest.json", "lean-toolchain"}
        required.update(p.relative_to(self.root / "lean").as_posix()
                        for p in (self.root / "lean/ComparatorChallenges").rglob("*.lean"))
        required.update(f"ComparatorChallenges/{name}.{suffix}" for name in CONFIG_NAMES
                        for suffix in ("lean", "json"))
        self.require(required <= set(artifacts), "Comparator report omits required fixture/helper bindings: "
                     + ", ".join(sorted(required - set(artifacts))))
        stale = []
        if proof_hash != self.proof_fingerprint():
            stale.append("proof_sources_sha256")
        for name, expected in artifacts.items():
            self.require(isinstance(expected, str) and re.fullmatch(r"[0-9a-f]{64}", expected),
                         f"Malformed Comparator artifact hash: {name}")
            self.require(isinstance(name, str) and not PurePosixPath(name).is_absolute()
                         and ".." not in PurePosixPath(name).parts and "\\" not in name,
                         f"Comparator artifact is not lean-relative: {name}")
            self.require(name != "ComparatorChallenges/verification-status.json", "Self-referential Comparator report hash")
            if digest(self.path("lean/" + name).read_bytes()) != expected:
                stale.append(name)
        if stale and self.allow_stale:
            self.warnings.append("Stale Comparator report accepted for preparation only: " + ", ".join(stale))
        else:
            self.require(not stale, "Comparator report is stale: " + ", ".join(stale))

    def nanoda(self):
        """Check immutable tool pins and recorded input bindings, never replay a proof."""
        pin = self.read_json("lean/ComparatorConfig/nanoda-toolchain.json")
        self.require(pin == NANODA_PIN, "Nanoda source/Rust/lockfile pin metadata differs")
        self.path("lean/ComparatorConfig/check_nanoda.py")
        name = "lean/ComparatorConfig/nanoda-status.json"
        if not (self.root / name).exists():
            metadata = self.text("formalization.yaml")
            self.require(self.allow_stale or name not in metadata,
                         "Formalization metadata references missing Nanoda evidence")
            self.warnings.append("Nanoda success evidence is absent; pin validation is not a checker run.")
            return
        report = self.read_json(name)
        self.require(report.get("schema_version") == 1 and report.get("status") == "passed",
                     "Nanoda report is not a successful version-1 execution record")
        self.require(report.get("mode") == "unsandboxed_independent_kernel"
                     and report.get("sandboxed_comparator") == "not_run",
                     "Nanoda evidence must not claim sandboxed Comparator verification")
        self.require(report.get("nanoda") == pin and report.get("lean_toolchain") == TOOLCHAIN,
                     "Nanoda result tool pins differ from the configured checker")
        axioms = report.get("permitted_axioms", [])
        self.require(isinstance(axioms, list) and len(axioms) == 3 and set(axioms) == ALLOWED_AXIOMS
                     and report.get("unpermitted_axiom_hard_error") is True,
                     "Nanoda must reject all axioms except the three recorded standard axioms")
        self.require(report.get("unknown_pp_declar_hard_error") is True,
                     "Nanoda must reject missing requested declarations")
        completed = datetime.datetime.fromisoformat(report["completed_at_utc"])
        self.require(completed.tzinfo is not None and completed.utcoffset() == datetime.timedelta(0),
                     "Nanoda completion time is not timezone-qualified UTC")
        for field in ("nanoda_binary_sha256", "proof_sources_sha256"):
            self.require(isinstance(report.get(field), str)
                         and re.fullmatch(r"[0-9a-f]{64}", report[field]),
                         f"Malformed Nanoda hash: {field}")
        stale = []
        if report["proof_sources_sha256"] != self.proof_fingerprint():
            stale.append("proof_sources_sha256")
        artifacts = report.get("artifact_sha256")
        required = {"ComparatorConfig/check_nanoda.py", "ComparatorConfig/nanoda-toolchain.json",
                    "lake-manifest.json", "lean-toolchain"}
        self.require(isinstance(artifacts, dict) and required <= set(artifacts),
                     "Nanoda report omits executed helper/toolchain bindings")
        for artifact, expected in artifacts.items():
            self.require(isinstance(artifact, str) and not PurePosixPath(artifact).is_absolute()
                         and ".." not in PurePosixPath(artifact).parts and "\\" not in artifact,
                         f"Nanoda artifact is not lean-relative: {artifact}")
            self.require(artifact != "ComparatorConfig/nanoda-status.json", "Self-referential Nanoda report hash")
            self.require(isinstance(expected, str) and re.fullmatch(r"[0-9a-f]{64}", expected),
                         f"Malformed Nanoda artifact hash: {artifact}")
            if digest(self.path("lean/" + artifact).read_bytes()) != expected:
                stale.append(artifact)
        cases = report.get("cases")
        expected_cases = {f"ComparatorChallenges/{config}.json" for config in CONFIG_NAMES}
        self.require(isinstance(cases, dict) and set(cases) == expected_cases,
                     "Nanoda evidence must cover all three configured solution cases")
        for config_path, case in cases.items():
            config = self.configs["lean/" + config_path]
            self.require(case.get("status") == "passed" and case.get("theorem_names") == config["theorem_names"],
                         f"Nanoda case has wrong status or theorem set: {config_path}")
            self.require(case.get("exported_theorems_present") is True,
                         f"Nanoda evidence does not confirm exported theorem roots: {config_path}")
            for field in ("config_sha256", "solution_export_sha256"):
                self.require(isinstance(case.get(field), str) and re.fullmatch(r"[0-9a-f]{64}", case[field]),
                             f"Malformed Nanoda case hash: {config_path}/{field}")
            self.require(type(case.get("export_bytes")) is int and case["export_bytes"] > 0,
                         f"Nanoda case has no nonempty proof export: {config_path}")
            if case["config_sha256"] != digest(self.path("lean/" + config_path).read_bytes()):
                stale.append(config_path)
        if stale and self.allow_stale:
            self.warnings.append("Stale Nanoda evidence accepted for preparation only: " + ", ".join(stale))
        else:
            self.require(not stale, "Nanoda report is stale: " + ", ".join(stale))

    def config_ref(self, path, declarations):
        self.path(path)
        self.require(path in self.configs, f"Not a validated Comparator runner config: {path}")
        self.require(set(declarations) & set(self.configs[path]["theorem_names"]),
                     f"Comparator config does not cover the mapped declaration: {path}")

    def mapping(self):
        data = self.read_json("metadata/natural-language-map.json")
        self.require(data["path_base"] == "repository root", "Unexpected mapping path base")
        manuscript = data["manuscript"]
        self.require(digest(self.path(manuscript["file"]).read_bytes()) == manuscript["sha256"],
                     "Mapping manuscript checksum differs")
        ids = [entry["id"] for entry in data["entries"]]
        self.require(len(ids) == len(set(ids)), "Duplicate mapping entry ids")
        for entry in data["entries"]:
            source = entry["manuscript"]
            lines = self.text(source["file"]).splitlines()
            for anchor in source["anchors"]:
                token = "\\label{" + anchor["label"] + "}"
                found = [i for i, line in enumerate(lines, 1) if token in line]
                self.require(type(anchor["line"]) is int and found == [anchor["line"]],
                             f"Missing, duplicated or stale TeX locator: {anchor}")
            for decl in entry["lean"]:
                self.require(self.module_file(decl["module"]) == decl["file"],
                             f"Module/file mismatch: {decl}")
                self.declared(decl["declaration"], decl["file"], decl["line"])
            if "comparator_config" in entry:
                self.config_ref(entry["comparator_config"], [d["declaration"] for d in entry["lean"]])
        formalization = self.read_yaml("formalization.yaml")
        status = formalization["status"]
        self.require(status["sorry_count"] == 0 and status["sorry_in_definitions"] == 0,
                     "Unexpected unresolved proof holes in metadata")
        self.require(set(status["axioms"]) == ALLOWED_AXIOMS, "Wrong formalization axiom policy")
        for result in status["main_results"]:
            self.declared(result["declaration"], result["file"])
            self.require(result["sorry_count"] == 0 and set(result["axioms"]) == ALLOWED_AXIOMS,
                         f"Unexpected proof status for {result['declaration']}")
            if "comparator_config" in result:
                self.config_ref(result["comparator_config"], [result["declaration"]])
        for key in ("mapping_file", "status_document"):
            self.path(formalization["alignment"][key])
        self.path("LICENSE"); self.path("NOTICE")
        if formalization["project"]["license"].lower() == "pending":
            self.warnings.append("License is pending: local preparation is permitted; validation is not publication approval.")

    def letter_sources(self):
        """Bind current companion sources and keep geometric claims separate."""
        filename = "metadata/letter-source-map.json"
        article = self.read_json("metadata/natural-language-map.json")
        self.require(article.get("companion_mapping_file") == filename,
                     "Missing or incorrect companion source-map reference")
        data = self.read_json(filename)
        self.require((data["format"], data["version"], data["path_base"]) ==
                     ("free-entropy-letter-map", 1, "repository root"),
                     "Unexpected companion mapping format")
        sources = data["source_files"]
        self.require(Counter(s["file"] for s in sources) ==
                     Counter(["article.tex", "letter.tex", "free.bib", "compression.pdf"]),
                     "Companion source inventory is incomplete or duplicated")
        by_file = {s["file"]: s for s in sources}
        for source in sources:
            self.require(digest(self.path(source["file"]).read_bytes()) == source["sha256"],
                         f"Companion source checksum differs: {source['file']}")
        self.require(data["manuscript"]["file"] == "letter.tex" and
                     data["manuscript"]["sha256"] == by_file["letter.tex"]["sha256"] and
                     article["manuscript"]["sha256"] == by_file["article.tex"]["sha256"],
                     "Inconsistent manuscript identity in companion map")
        formalization = self.read_yaml("formalization.yaml")
        letter_id = "letter.tex; SHA-256 " + by_file["letter.tex"]["sha256"]
        self.require(sum(s.get("id") == letter_id for s in formalization["sources"]) == 1,
                     "formalization.yaml does not identify the current Letter")
        article_entries = {e["id"]: e for e in article["entries"]}
        entries = data["entries"]
        ids = [entry["id"] for entry in entries]
        self.require(entries and len(ids) == len(set(ids)), "Empty or duplicate Letter entry ids")
        lines = self.text("letter.tex").splitlines()
        statuses = {"consequence-of-article", "definition-correspondence", "not-formalized"}
        for entry in entries:
            self.require(entry["status"] in statuses, f"Unknown Letter coverage: {entry['id']}")
            self.require(entry["manuscript"]["file"] == "letter.tex", "Unexpected Letter entry source")
            self.require(entry["manuscript"]["anchors"], "Letter entry has no source anchor")
            for anchor in entry["manuscript"]["anchors"]:
                token = "\\label{" + anchor["label"] + "}"
                found = [i for i, line in enumerate(lines, 1) if token in line]
                self.require(type(anchor["line"]) is int and found == [anchor["line"]],
                             f"Missing, duplicated or stale Letter locator: {anchor}")
            refs = entry["article_entries"]
            self.require(len(refs) == len(set(refs)) and set(refs) <= set(article_entries),
                         f"Unknown/duplicate Article correspondence: {entry['id']}")
            if entry["status"] == "consequence-of-article":
                expected = [d for ref in refs for d in article_entries[ref]["lean"]]
                self.require(refs and entry["lean"] == expected,
                             f"Letter consequence does not match Article declarations: {entry['id']}")
                for decl in entry["lean"]:
                    self.require(self.module_file(decl["module"]) == decl["file"],
                                 f"Module/file mismatch: {decl}")
                    self.declared(decl["declaration"], decl["file"], decl["line"])
            else:
                self.require(entry["lean"] == [],
                             f"Uncertified Letter claim has direct Lean certificates: {entry['id']}")
        self.require("\\includegraphics[width=\\linewidth]{compression.pdf}" in "\n".join(lines)
                     and "\\bibliography{free}" in "\n".join(lines),
                     "Letter dependency inventory needs updating")

    def pins(self):
        self.require(self.text("lean/lean-toolchain").strip() == TOOLCHAIN, "Lean toolchain pin changed")
        lock = self.read_json("lean/lake-manifest.json")
        packages = lock["packages"]
        self.require(len({p["name"] for p in packages}) == len(packages), "Duplicate dependency package")
        by_name = {p["name"]: p for p in packages}
        for package in packages:
            self.require(package["type"] == "git" and re.fullmatch(r"[0-9a-f]{40}", package["rev"])
                         and package["url"].startswith("https://github.com/"),
                         f"Unpinned/non-public dependency: {package['name']}")
        self.require(by_name["mathlib"]["rev"] == MATHLIB_REVISION, "Mathlib pin changed")
        self.require(by_name["Comparator"]["rev"] == COMPARATOR_REVISION, "Comparator pin changed")
        lake = tomllib.loads(self.text("lean/lakefile.toml"))
        for dep in lake["require"]:
            self.require(dep["name"] in by_name and dep["rev"] == by_name[dep["name"]]["rev"],
                         f"Lake/manifest revision mismatch: {dep['name']}")
            self.require(dep["git"].removesuffix(".git") ==
                         by_name[dep["name"]]["url"].removesuffix(".git"),
                         f"Lake/manifest URL mismatch: {dep['name']}")

    def audit(self):
        path = self.root / "lean/verification/summary.json"
        if not path.exists() and self.allow_stale:
            self.warnings.append("Audit summary is absent; preparation mode does not establish a proof verification result.")
            return
        summary = self.read_json("lean/verification/summary.json")
        self.require(summary.get("status") == "passed", "Audit summary does not report a passing audit")
        proof_files = sorted((self.root / "lean/FreeEntropy").glob("*.lean"))
        source_hash = self.proof_fingerprint()
        kinds = Counter(kind for file, index in self.decls.items() if file.startswith("lean/FreeEntropy/")
                        for kind, _ in index.values() if kind in {"theorem", "lemma", "def", "abbrev"})
        expected = {
            "proof_sources_sha256": source_hash,
            "lean_modules": len(proof_files),
            "proved_declarations_audited": kinds["theorem"] + kinds["lemma"],
            "total_public_declarations_audited": sum(kinds.values()),
            "lean_toolchain": TOOLCHAIN,
            "mathlib_revision": MATHLIB_REVISION,
            "manuscript_sha256": digest(self.path("article.tex").read_bytes()),
        }
        wrong = [key for key, value in expected.items() if summary.get(key) != value]
        self.require(set(summary.get("allowed_axioms", [])) == ALLOWED_AXIOMS, "Unexpected audit axiom policy")
        if wrong and self.allow_stale:
            self.warnings.append("Stale audit evidence accepted for preparation only: " + ", ".join(wrong))
        else:
            self.require(not wrong, "Audit summary is stale: " + ", ".join(wrong) + "; rerun lean/check.sh")
        # A source release may include the summary without the large raw logs.
        # When the axiom log is present, reject explicit failures/unexpected axioms.
        report_path = self.root / "lean/verification/axioms.txt"
        if report_path.is_file():
            report = self.text("lean/verification/axioms.txt")
            self.require(not re.search(r"sorryAx|admitAx|error:", report), "Axiom log contains an error/placeholder")
            groups = re.findall(r"depends? on axioms:\s*\[([^]]*)\]", report)
            self.require(groups, "Axiom log has no completed dependency output")
            for group in groups:
                self.require({x.strip() for x in group.split(",") if x.strip()} <= ALLOWED_AXIOMS,
                             "Axiom log reports an unexpected axiom")
        self.audit_current = not wrong

    def proof_catalog(self):
        """Validate generated documentation bindings, without executing Lean."""
        script = self.path("scripts/generate_proof_catalog.py")
        result = subprocess.run(
            [sys.executable, str(script), "--check", "--root", str(self.root)],
            capture_output=True, text=True, check=False,
        )
        self.require(result.returncode == 0,
                     "Proof catalog is stale or invalid: " +
                     (result.stderr or result.stdout).strip())

    def run(self):
        self.check("official metadata schemas", self.schemas)
        self.check("Lean source index", self.load_sources)
        self.check("production import boundary", self.boundaries)
        self.check("copyright and attribution headers", self.headers)
        self.check("Comparator configuration and declaration names", self.comparator)
        self.check("Nanoda pins and execution-evidence bindings", self.nanoda)
        self.check("manuscript and theorem mappings", self.mapping)
        self.check("companion Letter source inventory and coverage", self.letter_sources)
        self.check("toolchain and dependency pins", self.pins)
        self.check("proof audit evidence", self.audit)
        if self.allow_stale and not self.audit_current:
            self.warnings.append("Compiled proof catalog validation is deferred until a current passing audit exists; rerun normal validation after lean/check.sh.")
        else:
            self.check("compiled proof catalog and source bindings", self.proof_catalog)
        for message in self.warnings:
            print("NOTE:", message)
        for message in self.errors:
            print("FAIL:", message, file=sys.stderr)
        if self.errors:
            print(f"FAILED: {len(self.errors)} artifact checks", file=sys.stderr)
            return 1
        mode = "preparation; stale/missing audit allowed" if self.allow_stale else "current passing audit required"
        print(f"PASS: {len(self.completed)} artifact checks ({mode}).")
        print("No Lean rebuild, Comparator or Nanoda execution was performed. Publication approval is not implied.")
        return 0


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", type=Path, default=Path(__file__).resolve().parents[1],
                        help="repository source root (defaults to this script's parent repository)")
    parser.add_argument("--allow-stale-audit", action="store_true",
                        help="preparation only: permit missing or stale passing audit evidence")
    parser.add_argument("--schema-cache", type=Path,
                        help="optional external schema cache, verified against pinned hashes")
    args = parser.parse_args()
    return Validator(args.root.resolve(), args.allow_stale_audit,
                     args.schema_cache.resolve() if args.schema_cache else None).run()


if __name__ == "__main__":
    sys.exit(main())
