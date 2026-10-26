#!/usr/bin/env python3
"""Check the live Chapter 10 integration against its reviewed source manifest.

This is a source/provenance gate, not a substitute for `cd rudin && lake build`.
The default Lean target checks contracts and all transitive axiom dependencies.
No snapshot tree, package download, or Git source checkout is used here.
"""

import hashlib
import json
from pathlib import Path
import re
import sys

from check_chapter01 import lean_code

ROOT = Path(__file__).resolve().parents[1]
MANIFEST = ROOT / "evidence/ch10-integration-manifest.json"


def check():
    manifest = json.loads(MANIFEST.read_text())
    errors = []

    def require(condition, message):
        if not condition:
            errors.append(message)

    for record in manifest["files"] + manifest["preserved_main_files"]:
        path = ROOT / record["path"]
        require(path.is_file(), f"Missing reviewed file: {record['path']}")
        if path.is_file():
            digest = hashlib.sha256(path.read_bytes()).hexdigest()
            require(digest == record["sha256"], f"Reviewed bytes changed: {record['path']}")

    lean_root = ROOT / "rudin"
    sources = sorted((lean_root / "Rudin").rglob("*.lean")) + [lean_root / "Rudin.lean"]
    code = {p: lean_code(p.read_text()) for p in sources}
    for path, text in code.items():
        for match in re.finditer(r"\b(?:sorry|admit|native_decide|sorryAx|axiom)\b", text):
            line = text.count("\n", 0, match.start()) + 1
            errors.append(f"Forbidden token {match.group()} at {path.relative_to(ROOT)}:{line}")

    chapter = [p for p in sources if p.name.startswith("Chapter10") or "Chapter10" in p.parts]
    require({str(p.relative_to(ROOT)) for p in chapter} == set(manifest["chapter10_files"]),
            "Chapter 10 file inventory differs from the reviewed manifest")
    joined = "\n".join(code[p] for p in chapter)
    principals = re.findall(r"\b(?:theorem|lemma)\s+pma10_(\d+)\s*(?=:)", joined)
    contracts = re.findall(r"\bdef\s+pma10_(\d+)_contract\s*(?=:)", joined)
    expected = {str(i) for i in range(1, 52)}
    require(len(principals) == 50 and set(principals) == expected - {"43"},
            "Require exactly 50 principal proofs, with only pma10_43 absent")
    require(len(contracts) == 51 and set(contracts) == expected,
            "Require all 51 distinct numbered contracts, including exact 10.43")
    for name in ["pma10_43_forward", "pma10_43_scalar_converse",
                 "vectorPotential_c1_of_equivalent_convex"]:
        require(re.search(r"\b(?:theorem|lemma)\s+" + name + r"\b", joined),
                f"Missing retained partial result: {name}")

    visited = set()
    pending = ["Rudin"]
    while pending:
        module = pending.pop()
        if module in visited:
            continue
        visited.add(module)
        path = lean_root / (module.replace(".", "/") + ".lean")
        require(path in code, f"Unresolved live-tree import: {module}")
        if path in code:
            pending.extend(re.findall(r"^import\s+(Rudin(?:\.[\w]+)*)\s*$", code[path], re.M))
    for path in chapter:
        module = str(path.relative_to(lean_root).with_suffix("")).replace("/", ".")
        require(module in visited, f"Chapter 10 module absent from default build: {module}")
    for module in ["Rudin.PMA.Chapter08Audit", "Rudin.PMA.Chapter09.FirstHalfAudit",
                   "Rudin.PMA.Chapter09.SecondHalfAudit", "Rudin.PMA.Chapter10.IntegrationAudit"]:
        require(module in visited, f"Required default-build audit missing: {module}")
    probes = [p for p in chapter if p.name.endswith("Probes.lean")]
    require(len(probes) == 25, "Require all 25 recovered Chapter 10 probe modules")
    progress = (ROOT / "PROGRESS.md").read_text()
    require(re.search(r"^\|\s*10\s*\|[^|]*\|\s*50\s*/\s*51\s*\|", progress, re.M),
            "PROGRESS.md must record 50 / 51 for Chapter 10")
    require("PMA-10.43" in (ROOT / "QUEUE.md").read_text(), "10.43 must remain visibly queued")
    if errors:
        for error in errors:
            print(f"ERROR: {error}", file=sys.stderr)
        return 1
    print(f"PASS: {len(chapter)} Chapter 10 modules, 25 probes, 51 contracts, 50 principals; "
          "10.43 partial state retained.")
    print(f"PASS: {len(sources)} live project Lean sources scanned; zero forbidden proof tokens; "
          "all Chapter 10 modules reachable from default Rudin target.")
    print(f"PASS: {len(manifest['files'])} integration file hashes and "
          f"{len(manifest['preserved_main_files'])} preserved main/pin hashes match.")
    return 0


if __name__ == "__main__":
    raise SystemExit(check())
