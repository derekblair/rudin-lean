#!/usr/bin/env python3
"""Check Chapter 1's node coverage, prohibited proof commands, and progress count.

Run from any directory. Use --partial while adding nodes; without that option all
37 numbered nodes must be present. The Lean Chapter01Audit module separately
checks transitive axiom dependencies and should be imported by Rudin.lean.
"""

from __future__ import annotations

import argparse
from pathlib import Path
import re
import sys


EXPECTED = [1, *range(3, 39)]
ROOT = Path(__file__).resolve().parents[1]


def lean_code(text: str) -> str:
    """Replace Lean comments and string literals with spaces, keeping line breaks."""
    result: list[str] = []
    i = 0
    depth = 0
    in_string = False
    while i < len(text):
        c = text[i]
        if depth:
            if text.startswith("/-", i):
                depth += 1
                result.extend("  ")
                i += 2
                continue
            if text.startswith("-/", i):
                depth -= 1
                result.extend("  ")
                i += 2
                continue
            result.append("\n" if c == "\n" else " ")
        elif in_string:
            if c == "\\" and i + 1 < len(text):
                result.extend("  ")
                i += 2
                continue
            if c == '"':
                in_string = False
            result.append("\n" if c == "\n" else " ")
        elif text.startswith("/-", i):
            depth = 1
            result.extend("  ")
            i += 2
            continue
        elif text.startswith("--", i):
            end = text.find("\n", i)
            if end < 0:
                result.extend(" " * (len(text) - i))
                break
            result.extend(" " * (end - i))
            i = end
            continue
        elif c == '"':
            in_string = True
            result.append(" ")
        else:
            result.append(c)
        i += 1
    if depth or in_string:
        raise ValueError("Chapter has an unterminated comment or string literal")
    return "".join(result)


def check(partial: bool) -> list[str]:
    errors: list[str] = []
    chapter_path = ROOT / "rudin/Rudin/PMA/Chapter01.lean"
    chapter = chapter_path.read_text()
    marker_matches = list(re.finditer(r"/-!\s+###\s+PMA-1\.(\d+)\b", chapter))
    nodes = [int(match.group(1)) for match in marker_matches]
    if len(nodes) != len(set(nodes)):
        errors.append("Chapter contains duplicate node markers")
    unexpected = sorted(set(nodes) - set(EXPECTED))
    if unexpected:
        errors.append(f"Unexpected numbered nodes: {unexpected}")
    if nodes != sorted(nodes):
        errors.append("Chapter node markers are not in dependency order")
    if not partial and nodes != EXPECTED:
        errors.append(f"Missing numbered nodes: {sorted(set(EXPECTED) - set(nodes))}")

    try:
        code = lean_code(chapter)
    except ValueError as exc:
        errors.append(str(exc))
        code = ""
    for match in re.finditer(r"\b(?:sorry|admit|native_decide|sorryAx|axiom)\b", code):
        line = code.count("\n", 0, match.start()) + 1
        errors.append(f"Prohibited proof/declaration token {match.group()} at line {line}")

    progress = (ROOT / "PROGRESS.md").read_text()
    count = re.search(r"^\|\s*01\s*\|[^|]*\|\s*(\d+)\s*/\s*(\d+)\s*\|\s*$", progress, re.M)
    if not count:
        errors.append("PROGRESS.md lacks the Chapter 01 completed/total count")
    elif (int(count.group(1)), int(count.group(2))) != (len(nodes), len(EXPECTED)):
        errors.append(f"PROGRESS.md has {count.group(1)}/{count.group(2)}; chapter has {len(nodes)}/37 nodes")

    inventory = (ROOT / "research/pma-ch01-inventory.md").read_text()
    inventoried = [int(n) for n in re.findall(r"^- \*\*PMA-1\.(\d+)\*\*", inventory, re.M)]
    if inventoried != EXPECTED:
        errors.append("Chapter 1 inventory does not match the 37 expected numbered nodes")

    queue = (ROOT / "QUEUE.md").read_text()
    queued = {int(n) for n in re.findall(r"^(?:#+\s+|[-*]\s+\*\*)PMA-1\.(\d+)\b", queue, re.M)}
    stale = sorted(queued & set(nodes))
    if stale:
        errors.append(f"QUEUE.md still lists completed nodes as blocked: {stale}")

    if not errors:
        state = "partial" if partial else "complete"
        print(f"Chapter 1 {state} source audit passed: {len(nodes)}/37 nodes, metadata consistent, no prohibited proof commands.")
    return errors


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--partial", action="store_true", help="allow an unfinished chapter while checking completed-node counts")
    args = parser.parse_args()
    errors = check(args.partial)
    for error in errors:
        print(f"ERROR: {error}", file=sys.stderr)
    return 1 if errors else 0


if __name__ == "__main__":
    sys.exit(main())
