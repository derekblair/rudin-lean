#!/usr/bin/env python3
"""Verify restored Chapter 10 bytes; optionally build a pinned dependency snapshot.

The snapshot supplements unavailable first-half/earlier-chapter prerequisites
from the recorded Git commit. A snapshot success is not a standalone-lane build
success. No package is downloaded and no other lane or chapter is modified.
"""

import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess

from check_chapter01 import lean_code


ROOT = Path(__file__).resolve().parents[1]
MANIFEST = ROOT / "evidence/ch10-b-reconciliation-manifest.json"
OWN_MODULES = ["rudin/Rudin/PMA/Chapter10/SecondHalf.lean",
               "rudin/Rudin/PMA/Chapter10/SecondHalfAudit.lean"]
PINS = ["rudin/lakefile.toml", "rudin/lake-manifest.json", "rudin/lean-toolchain"]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--build-snapshot", action="store_true")
    args = parser.parse_args()
    manifest = json.loads(MANIFEST.read_text())
    commit = manifest["source_commit"]

    def git_bytes(path):
        return subprocess.check_output(["git", "show", f"{commit}:{path}"], cwd=ROOT)

    sources = {}
    for record in manifest["restored_files"] + manifest["dependency_files"]:
        path = record["path"]
        data = git_bytes(path)
        assert hashlib.sha256(data).hexdigest() == record["sha256"], path
        assert len(data) == record["bytes"], path
        sources[path] = data
    for record in manifest["restored_files"]:
        path = record["path"]
        assert (ROOT / path).read_bytes() == sources[path], f"Reused file changed: {path}"
    checked_paths = [r["path"] for r in manifest["restored_files"]] + OWN_MODULES
    for path in checked_paths:
        code = lean_code((ROOT / path).read_text())
        bad = re.findall(r"\b(?:sorry|admit|native_decide|sorryAx|axiom)\b", code)
        assert not bad, (path, bad)
    for path in PINS:
        assert (ROOT / path).read_bytes() == git_bytes(path), f"Pin changed: {path}"
    print(f"PASS: {len(manifest['restored_files'])} restored modules match {commit}; "
          f"{len(checked_paths)} lane Lean files have no forbidden proof tokens; "
          "all dependency hashes and project pins match.", flush=True)
    if not args.build_snapshot:
        return 0

    snapshot = ROOT / ".ch10-b-validation"
    for path, data in sources.items():
        destination = snapshot / path
        destination.parent.mkdir(parents=True, exist_ok=True)
        destination.write_bytes(data)
    # Include the actual first-half modules after their branch is rebased in,
    # including any additional first-half wrapper not present in the old tree.
    # Only absent prerequisites are supplied from the recorded source commit.
    for path in (ROOT / "rudin/Rudin/PMA/Chapter10").glob("*.lean"):
        destination = snapshot / path.relative_to(ROOT)
        destination.parent.mkdir(parents=True, exist_ok=True)
        destination.write_bytes(path.read_bytes())
    for path in OWN_MODULES + PINS + ["rudin/Rudin/PMA/Chapter10.lean"]:
        destination = snapshot / path
        destination.parent.mkdir(parents=True, exist_ok=True)
        destination.write_bytes((ROOT / path).read_bytes())
    lake_dir = snapshot / "rudin/.lake"
    lake_dir.mkdir(exist_ok=True)
    packages = lake_dir / "packages"
    if not packages.exists():
        packages.symlink_to(ROOT / "rudin/.lake/packages", target_is_directory=True)
    print("Snapshot adds exact prior prerequisites; standalone build is a separate check.",
          flush=True)
    return subprocess.run(
        ["lake", "build", "Rudin.PMA.Chapter10.SecondHalf",
         "Rudin.PMA.Chapter10.SecondHalfAudit"],
        cwd=snapshot / "rudin", env=dict(os.environ, LEAN_NUM_THREADS="1"),
        check=False).returncode


if __name__ == "__main__":
    raise SystemExit(main())
