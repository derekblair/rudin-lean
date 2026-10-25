#!/usr/bin/env python3
"""Check reused Chapter 10 bytes and optionally build with exact prior prerequisites.

The standalone lane deliberately does not modify other chapters. --build prepares
an ignored snapshot inside this lane, taking prerequisites from the recorded Git
commit, Chapter 10 from this lane, and the already-installed pinned Mathlib cache.
It never fetches, installs packages, changes branches, or edits another lane.
"""

from pathlib import Path
import argparse
import hashlib
import json
import os
import re
import subprocess
import sys

sys.dont_write_bytecode = True
from check_chapter01 import lean_code

ROOT = Path(__file__).resolve().parents[1]
MANIFEST = ROOT / "evidence/ch10-a-reconciliation-manifest.json"


def git_bytes(commit, path):
    return subprocess.check_output(["git", "show", f"{commit}:{path}"], cwd=ROOT)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--build", action="store_true")
    args = parser.parse_args()
    manifest = json.loads(MANIFEST.read_text())
    commit = manifest["source_commit"]
    errors = []
    chapter_paths = []
    for record in manifest["files"]:
        path = record["path"]
        source = git_bytes(commit, path)
        if hashlib.sha256(source).hexdigest() != record["sha256"]:
            errors.append(f"Recorded source hash differs: {path}")
        if "/Chapter10/" in path:
            chapter_paths.append(path)
            if not (ROOT / path).is_file() or (ROOT / path).read_bytes() != source:
                errors.append(f"Reused Chapter 10 source differs: {path}")
    chapter_paths += ["rudin/Rudin/PMA/Chapter10.lean", "rudin/Rudin/PMA/Chapter10Audit.lean"]
    chapter_paths += manifest.get("additional_lane_modules", [])
    for record in manifest.get("additional_lane_module_hashes", []):
        if hashlib.sha256((ROOT / record["path"]).read_bytes()).hexdigest() != record["sha256"]:
            errors.append(f"Supplementary source hash differs: {record['path']}")
    for path in chapter_paths:
        code = lean_code((ROOT / path).read_text())
        bad = re.findall(r"\b(?:sorry|admit|native_decide|sorryAx|axiom)\b", code)
        if bad:
            errors.append(f"Forbidden proof tokens in {path}: {bad}")
    pins = ["rudin/lakefile.toml", "rudin/lake-manifest.json", "rudin/lean-toolchain"]
    for path in pins:
        if (ROOT / path).read_bytes() != git_bytes(commit, path):
            errors.append(f"Toolchain/package pin differs from reconciled source: {path}")
    if errors:
        print("\n".join(errors), file=sys.stderr)
        return 1
    print(f"PASS: {len(manifest['files'])} provenance hashes; "
          f"{len(chapter_paths) - 2 - len(manifest.get('additional_lane_modules', []))} reused Chapter 10 modules; "
          f"{len(manifest.get('additional_lane_modules', []))} supplementary modules; "
          "no forbidden proof tokens; unchanged pins.", flush=True)
    if not args.build:
        return 0
    validation = ROOT / ".lane-validation"
    for record in manifest["files"]:
        path = record["path"]
        destination = validation / path
        destination.parent.mkdir(parents=True, exist_ok=True)
        destination.write_bytes((ROOT / path).read_bytes() if "/Chapter10/" in path
                                else git_bytes(commit, path))
    for path in pins + chapter_paths:
        destination = validation / path
        destination.parent.mkdir(parents=True, exist_ok=True)
        destination.write_bytes((ROOT / path).read_bytes())
    lake_dir = validation / "rudin/.lake"
    lake_dir.mkdir(exist_ok=True)
    packages = lake_dir / "packages"
    if not packages.exists():
        packages.symlink_to(ROOT / "rudin/.lake/packages", target_is_directory=True)
    env = dict(os.environ, LEAN_NUM_THREADS="1")
    result = subprocess.run(
        ["lake", "build", "Rudin.PMA.Chapter10", "Rudin.PMA.Chapter10Audit"],
        cwd=validation / "rudin", env=env, check=False)
    return result.returncode


if __name__ == "__main__":
    raise SystemExit(main())
