#!/usr/bin/env python3
"""Prime local Lean modules in dependency order, then run the requested Lake build.

Keeps only one local module compiler active on shared machines. Dependencies
outside this project must already have their pinned precompiled cache.
"""
from pathlib import Path
import os
import re
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[1] / 'rudin'
targets = sys.argv[1:] or ['Rudin']
seen = set()
order = []

def visit(module):
    if module in seen:
        return
    seen.add(module)
    path = ROOT / (module.replace('.', '/') + '.lean')
    if not path.is_file():
        raise SystemExit(f'Missing local module: {module}')
    for dependency in re.findall(r'^import (Rudin(?:\.[A-Za-z0-9_]+)*)\s*$', path.read_text(), re.M):
        visit(dependency)
    order.append(module)

for target in targets:
    visit(target)
env = dict(os.environ, LEAN_NUM_THREADS='1')
for module in order:
    print(f'Sequential module: {module}', flush=True)
    subprocess.run(['lake', 'build', module], cwd=ROOT, env=env, check=True)
print('Final requested build', flush=True)
subprocess.run(['lake', 'build'] + sys.argv[1:], cwd=ROOT, env=env, check=True)
