#!/usr/bin/env python3
"""Compile-free source checks. No Lean, Cargo, Kani or host command is invoked."""
import argparse
import hashlib
import json
from pathlib import Path
import re
import subprocess

parser = argparse.ArgumentParser()
parser.add_argument('--check', action='store_true')
args = parser.parse_args()
root = Path(__file__).resolve().parent
repo = root.parent.parent
rows = []
for path in sorted((root / 'pending-proof-sources').glob('*.lean.txt')):
    source = path.read_text()
    declarations = re.findall(r'^(?:theorem|def)\s+(\w+)', source, re.M)
    theorems = re.findall(r'^theorem\s+(\w+)', source, re.M)
    printed = re.findall(r'^#print axioms\s+(\w+)', source, re.M)
    missing = sorted(set(theorems) - set(printed))
    code = re.sub(r'/\-[\s\S]*?\-/|--[^\n]*', '', source)
    forbidden = re.findall(r'\b(?:sorry|admit|native_decide|implemented_by)\b|^\s*axiom\s+', code, re.M)
    overrides = re.findall(r'set_option\s+(?:maxHeartbeats|maxRecDepth)', source)
    assert not missing, (path, 'missing axiom prints', missing)
    assert not forbidden, (path, 'forbidden mechanism', forbidden)
    assert not overrides, (path, 'resource overrides', overrides)
    rows.append(dict(path=str(path.relative_to(repo)), sha256=hashlib.sha256(path.read_bytes()).hexdigest(),
        declarations=declarations, axioms_requests=printed, status='DRAFT_NOT_COMPILED',
        imports=re.findall(r'^import\s+(\S+)', source, re.M)))
# Confirm that the accepted trust contract is unchanged since resume entry.
trust = 'docs/research/v8-r0-zk-20261009/lean/R1Z/PV_RunJoin_TrustItems.lean'
entry = subprocess.check_output(['git', 'show', '3478e00a58:' + trust], cwd=repo)
assert entry == (repo / trust).read_bytes(), 'T changed'
record = dict(kind='compile-free-preparation-check', kernel_validation=False,
    entry_revision='3478e00a58', trust_unchanged=True, drafts=rows,
    lean_attempts=0, kani_runs=0, endpoint_premises_removed=0,
    endpoint_counts=dict(runtime_boundary=[2, 2], fields=[8, 8], native_residuals=[6, 6]))
output = root / 'preparation-audit.json'
if args.check:
    assert output.exists(), 'run without --check to create the audit'
    assert json.loads(output.read_text()) == record, 'draft/audit mismatch'
else:
    output.write_text(json.dumps(record, indent=2) + '\n')
print(f'{len(rows)} uncompiled drafts checked; T unchanged; no compiler or host job invoked')
