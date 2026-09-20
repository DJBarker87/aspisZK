#!/usr/bin/env python3
"""Check the memory-bounded copy retains every original declaration/proof."""
import argparse
import hashlib
from pathlib import Path
import subprocess

p = argparse.ArgumentParser()
p.add_argument('--repo', type=Path, required=True)
p.add_argument('--cached-workspace', type=Path, required=True)
args = p.parse_args()
revision = '406790e520fa48da4ed7ed0a8e0bb27b9d23625d'
relative = 'AspisFormal/AspisFormal/CircleNaturalBasis.lean'
original = subprocess.check_output(
    ['git', '-C', str(args.repo), 'show', f'{revision}:{relative}'])
assert hashlib.sha256(original).hexdigest() == \
    'bbf1448991e8e439db752fcd7c2f140dff7aeddae8c68953203b73c073e99271'
imports = b'''import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Combinatorics.Colex
'''
actual = (Path(__file__).resolve().parent.parent /
          'lean/AspisV8R16/NaturalBasisCore.lean').read_bytes()
assert actual == original.replace(b'import Mathlib\n', imports, 1)
evaluator = args.cached_workspace / 'AspisFormal/CircleNaturalBasisEval.lean'
assert hashlib.sha256(evaluator.read_bytes()).hexdigest() == \
    '127ea451736936d8fb077e065efb7d49719af776b3782dc82af4b97076be3a9a'
print('PASS: source-exact natural-basis declarations/proofs; evaluator source pin matches')
