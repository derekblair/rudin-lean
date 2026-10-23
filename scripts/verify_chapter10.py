#!/usr/bin/env python3
"""Verify reviewed Chapter 10 bytes, contracts, source guards and preserved inputs.

This is a source/integrity gate, not a substitute for the Lean audit or build.
"""
from pathlib import Path
import hashlib
import json
import re
import subprocess
from check_chapter01 import lean_code

ROOT = Path(__file__).resolve().parents[1]
EVIDENCE = ROOT / 'evidence'

def digest(data):
    return hashlib.sha256(data).hexdigest()

def main():
    reviewed = json.loads((EVIDENCE / 'ch10-reviewed-production-manifest.json').read_text())
    accepted = json.loads((EVIDENCE / 'ch10-accepted-contract-snapshot.json').read_text())
    preserved = json.loads((EVIDENCE / 'ch10-preserved-chapters.json').read_text())
    report = {'base': preserved['base'], 'reviewed_modules': {}, 'accepted_contracts': {},
              'preserved_files': {}, 'preserved_pins': {}, 'source_files': {}}
    for row in reviewed['files']:
        actual = digest((ROOT / row['path']).read_bytes())
        assert actual == row['sha256'], f"Reviewed bytes changed: {row['path']}"
        report['reviewed_modules'][row['path']] = actual
    for row in accepted['files']:
        source = (ROOT / row['path']).read_text()
        for name, contract in row['contracts'].items():
            text = contract['text']
            assert digest(text.encode()) == contract['sha256'], f'Bad accepted hash: {name}'
            assert source.count(text.rstrip()) == 1, f'Accepted contract absent or ambiguous: {name}'
            assert len(re.findall(r'^def ' + re.escape(name) + r'\b', source, re.M)) == 1
            report['accepted_contracts'][name] = contract['sha256']
    for row in preserved['unchanged_files']:
        actual = digest((ROOT / row['path']).read_bytes())
        assert actual == row['sha256'], f"Preserved source changed: {row['path']}"
        report['preserved_files'][row['path']] = actual
    for path in ('rudin/lean-toolchain', 'rudin/lakefile.toml', 'rudin/lake-manifest.json'):
        baseline = subprocess.check_output(['git', 'show', preserved['base'] + ':' + path], cwd=ROOT)
        actual = (ROOT / path).read_bytes()
        assert actual == baseline, f'Pinned input changed: {path}'
        report['preserved_pins'][path] = digest(actual)
    paths = [ROOT / 'rudin/Rudin/PMA/Chapter10.lean', ROOT / 'rudin/Rudin/PMA/Chapter10Audit.lean']
    paths.extend(sorted((ROOT / 'rudin/Rudin/PMA/Chapter10').glob('*.lean')))
    forbidden = r'\b(?:sorry|admit|sorryAx|native_decide|axiom|unsafe|implemented_by)\b'
    integrated = {row['path'] for row in reviewed['files']}
    integrated.update({'rudin/Rudin/PMA/Chapter10.lean', 'rudin/Rudin/PMA/Chapter10Audit.lean'})
    audit = (ROOT / 'rudin/Rudin/PMA/Chapter10Audit.lean').read_text()
    for module in re.findall(r'^import (Rudin\.PMA\.Chapter10\.[\w]+)$', audit, re.M):
        integrated.add('rudin/' + module.replace('.', '/') + '.lean')
    for path in paths:
        code = lean_code(path.read_text())
        assert not re.search(forbidden, code), f'Forbidden proof mechanism: {path}'
        relative = str(path.relative_to(ROOT))
        if relative in integrated:
            report['source_files'][relative] = digest(path.read_bytes())
    principals = re.findall(r'/-!\s+###\s+PMA-10\.(\d+)\b', paths[0].read_text())
    assert [int(i) for i in principals] == list(range(1, len(principals) + 1)), 'Book-order prefix violated'
    for i in principals:
        assert f'pma10_{i}_contract' in report['accepted_contracts'], f'No accepted contract for {i}'
    report['completed_prefix'] = [int(i) for i in principals]
    report['status'] = 'PASS: source and reviewed-byte integrity; Lean audit/build are separate gates'
    print(json.dumps(report, indent=2))

if __name__ == '__main__':
    main()
