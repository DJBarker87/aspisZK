#!/usr/bin/env python3
"""Read-only source/evidence audit. No compiler, prover, or host work."""
from pathlib import Path
import hashlib
import json
import subprocess
import time

start = time.monotonic()
root = Path(__file__).resolve().parents[2]
evidence = root / 'evidence/pool-scope-20261026'
pins = json.loads((evidence / 'PoolS_source-pins.json').read_text())
errors = []
for path, pin in pins['files'].items():
    data = (root / path).read_bytes()
    if hashlib.sha256(data).hexdigest() != pin['sha256'] or len(data) != pin['bytes']:
        errors.append(f'source changed: {path}')
manifest = json.loads((root / 'evidence/lowering2-20261026/Low2_build_manifest.json').read_text())
input_counts = []
for build in manifest['builds']:
    input_counts.append(len(build['repository_compiler_inputs']))
    for pin in build['repository_compiler_inputs']:
        if hashlib.sha256((root / pin['path']).read_bytes()).hexdigest() != pin['sha256']:
            errors.append(f'inherited input mismatch: {pin["path"]}')
diff = subprocess.check_output(['git', 'diff', '--name-only', pins['revision']], cwd=root, text=True).splitlines()
for path in diff:
    if not (path.startswith('evidence/pool-scope-20261026/PoolS_') or path == 'design/POOL-LIFECYCLE-SCOPE-20261026.md'):
        errors.append(f'outside assigned scope: {path}')
scan = json.loads((evidence / 'PoolS_surface-scan.json').read_text())
for item in scan['files']:
    if hashlib.sha256((root / item['path']).read_bytes()).hexdigest() != item['source_sha256']:
        errors.append(f'scan input changed: {item["path"]}')
text = (root / 'design/POOL-LIFECYCLE-SCOPE-20261026.md').read_text()
for row in ['V0','V1','V2','V3',*[f'P{i}' for i in range(12)],'H1','H2','C1','C2','R1','R2','R3','R4']:
    if text.count(f'| {row} |') != 1:
        errors.append(f'missing/duplicate inventory row: {row}')
check = subprocess.run(['git','diff','--check',pins['revision'],'--','design/POOL-LIFECYCLE-SCOPE-20261026.md','evidence/pool-scope-20261026'],cwd=root,capture_output=True,text=True)
if check.returncode:
    errors.append(check.stdout + check.stderr)
result = {
    'claim': 'source freeze, inherited compiler-input equality, mutation-scan input identity, row completeness, assigned diff scope and whitespace only; no semantic proof',
    'source_revision': pins['revision'],
    'audit_revision_anchor': subprocess.check_output(['git','rev-parse','HEAD'],cwd=root,text=True).strip(),
    'inherited_input_counts': input_counts,
    'Lean_invocations': 0, 'Kani_runs': 0, 'Rust_builds': 0,
    'formal_metrics': {'target': None,'exit': None,'wall': None,'peak_RSS': None,'swap': None,'print_axioms': 'not applicable; no new theorem'},
    'inspection_wall_seconds': time.monotonic() - start,
    'errors': errors, 'exit': int(bool(errors)),
}
(evidence / 'PoolS_validation.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result,indent=2))
raise SystemExit(bool(errors))
