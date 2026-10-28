#!/usr/bin/env python3
"""Author source inventory and preservation check; no Lean evaluation."""
import hashlib
import json
from pathlib import Path
import re
import subprocess

here = Path(__file__).resolve()
repo = next((p for p in here.parents if (p / '.git').exists()), here.parent.parent / 'repo')
base = 'c9d55a22e4a060c24bf754235bad24ab5deb71cf'
module = 'rudin/Rudin/Research/PMA1043ProofAttack.lean'
paths = [module, 'rudin/lean-toolchain', 'rudin/lakefile.toml',
         'rudin/lake-manifest.json', 'rudin/Rudin/Research/PMA1043Compatibility.lean',
         'rudin/Rudin/PMA/Chapter10/VectorPotentials.lean']
def git(*args):
    return subprocess.check_output(['git', '-C', str(repo), *args], text=True).strip()
source = (repo / module).read_text()
tokens = re.findall(r'\b(?:sorry|admit|sorryAx|axiom|native_decide|ofReduceBool|implemented_by|unsafe)\b', source)
assert not tokens, tokens
namespace = ''
declarations = []
for line in source.splitlines():
    if line.startswith('namespace '):
        namespace = line.split()[1]
    match = re.match(r'(def|lemma|theorem) ([A-Za-z0-9_]+)', line)
    if match:
        declarations.append({'kind': match[1], 'name': namespace + '.' + match[2]})
prints = re.findall(r'^#print axioms (\S+)$', source, re.M)
assert prints == [d['name'] for d in declarations]
preserved = [p for p in paths if p != module]
for path in preserved:
    original = subprocess.check_output(['git', '-C', str(repo), 'show', base + ':' + path])
    assert original == (repo / path).read_bytes(), path
changed = git('diff', '--name-only', base).splitlines()
assert all(p == module or p.startswith(('research/', 'evidence/')) for p in changed), changed
record = {
    'base_commit': base, 'branch': git('branch', '--show-current'),
    'toolchain_pin': (repo / 'rudin/lean-toolchain').read_text().strip(),
    'mathlib_checkout': subprocess.check_output(['git', '-C', str(repo / 'rudin/.lake/packages/mathlib'), 'rev-parse', 'HEAD'], text=True).strip(),
    'sha256': {p: hashlib.sha256((repo / p).read_bytes()).hexdigest() for p in paths},
    'preserved_byte_for_byte': preserved,
    'tracked_changes_since_base': changed,
    'forbidden_tokens': tokens,
    'explicit_declaration_count': len(declarations),
    'proved_declaration_count': sum(d['kind'] != 'def' for d in declarations),
    'printed_dependency_count': len(prints),
    'declarations': declarations,
}
print(json.dumps(record, indent=2))
