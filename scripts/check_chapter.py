#!/usr/bin/env python3
"""Check a PMA chapter against its extracted inventory and progress metadata."""
from pathlib import Path
import argparse
import re
import sys
from check_chapter01 import lean_code

ROOT = Path(__file__).resolve().parents[1]

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('chapter', type=int, choices=range(1,12))
    parser.add_argument('--partial', action='store_true')
    args = parser.parse_args()
    nn = f'{args.chapter:02d}'
    inventory_path = ROOT / f'research/pma-ch{nn}-inventory.md'
    chapter_path = ROOT / f'rudin/Rudin/PMA/Chapter{nn}.lean'
    if not inventory_path.exists():
        parser.error(f'Missing inventory: {inventory_path}')
    inventory = inventory_path.read_text()
    expected = re.findall(r'^- \*\*(PMA-\d+\.\d+(?:-[a-z]+)?)\*\*', inventory, re.M)
    chapter = chapter_path.read_text()
    found = re.findall(r'/-!\s+###\s+(PMA-\d+\.\d+(?:-[a-z]+)?)\b', chapter)
    errors = []
    if not expected or len(expected) != len(set(expected)):
        errors.append('Inventory missing nodes or containing duplicate identifiers')
    if len(found) != len(set(found)):
        errors.append('Duplicate chapter node markers')
    if any(not n.startswith(f'PMA-{args.chapter}.') for n in expected + found):
        errors.append('A node has the wrong chapter number')
    if any(n not in expected for n in found):
        errors.append('Source has nodes not found in inventory')
    order_section = re.search(r'^## Formalization order\n(.*)', inventory, re.M | re.S)
    planned = re.findall(r'`(PMA-\d+\.\d+(?:-[a-z]+)?)`', order_section.group(1)) if order_section else expected
    if len(planned) != len(set(planned)) or set(planned) != set(expected):
        errors.append('Formalization order must list every inventory node exactly once')
    if found != [n for n in planned if n in found]:
        errors.append('Source nodes differ from the declared dependency order')
    queue = (ROOT / 'QUEUE.md').read_text()
    queued = set(re.findall(r'^(?:#+\s+|[-*]\s+\*\*)(PMA-\d+\.\d+(?:-[a-z]+)?)\b', queue, re.M))
    if queued.intersection(found):
        errors.append('Completed nodes are still in the needs-insight queue')
    if not args.partial:
        missing = set(expected) - set(found) - queued
        if missing:
            errors.append(f'Nodes neither completed nor queued: {sorted(missing)}')
    for path in [chapter_path, ROOT / f'rudin/Rudin/PMA/Chapter{nn}Probes.lean']:
        if not path.exists():
            continue
        code = lean_code(path.read_text())
        for match in re.finditer(r'\b(?:sorry|admit|native_decide|sorryAx|axiom)\b', code):
            line = code.count('\n',0,match.start())+1
            errors.append(f'Forbidden token {match.group()} in {path.name}:{line}')
    progress = (ROOT / 'PROGRESS.md').read_text()
    count = re.search(r'^\|\s*'+nn+r'\s*\|[^|]*\|\s*(\d+)\s*/\s*(\d+)\s*\|\s*$', progress, re.M)
    if not count or (int(count.group(1)),int(count.group(2))) != (len(found),len(expected)):
        errors.append(f'PROGRESS.md must record {len(found)} / {len(expected)}')
    for error in errors:
        print(f'ERROR: {error}',file=sys.stderr)
    if errors:
        return 1
    print(f'Chapter {nn}: {len(found)}/{len(expected)} completed, {len(queued.intersection(expected))} queued; source and metadata checks pass.')
    return 0

if __name__=='__main__':
    sys.exit(main())
