#!/usr/bin/env python3
"""Focused consistency/path/evidence check; never reruns the data audit."""
import ast
import collections
import hashlib
import json
from pathlib import Path
import resource
import subprocess
import sys
import time

start = time.monotonic()
R = Path(__file__).resolve().parents[2]
T = R / 'tools/port29sdkdata-20261025'
E = R / 'evidence/port29sdkdata-20261025'
allowed = ('tools/port29sdkdata-20261025/', 'evidence/port29sdkdata-20261025/')


def pin(p):
    h = hashlib.sha256()
    with p.open('rb') as f:
        for b in iter(lambda: f.read(1024*1024), b''):
            h.update(b)
    return dict(path=str(p), bytes=p.stat().st_size, sha256=h.hexdigest())


audit = json.loads((E / 'Port29SDKDATA_audit.json').read_text())
for p in audit['retained_outputs']:
    assert pin(Path(p['path'])) == p
for d, source in [(audit, 'Port29SDKDATA_audit.py'),
                  (json.loads((E / 'Port29SDKDATA_sources.json').read_text()), 'Port29SDKDATA_sources.py'),
                  (json.loads((E / 'Port29SDKDATA_coverage.json').read_text()), 'Port29SDKDATA_coverage.py')]:
    assert d['exit_status'] == 0 and d.get('lean_invocations', 0) == 0 and d['swaps'] == 0
    assert d.get('tool_sha256', d.get('tool', {}).get('sha256')) == pin(T / source)['sha256']
rows = json.loads((E / 'Port29SDKDATA_missing-323.json').read_text())
assert len(rows) == len({r['name'] for r in rows}) == 323
assert sum(bool(r['current_modules']) for r in rows) == 265
assert sum(bool(r['port18_released_manifest_origin']) for r in rows) == 243
assert all(not r['old_name_absence_proved'] and r['strict_sameDeclaration'] == 'NOT RUN' for r in rows)
assert audit['proposed_union']['raw_missing'] == 77
assert audit['proposed_union']['prior_core_leaf_body_missing'] == 23
assert len(audit['proposed_union']['residual_names']) == 54
assert audit['pair_candidates'] == 1059 and audit['edge_different_pairs'] == 550
assert not audit['proposed_union']['safe_logical_closure']
run = json.loads((E / 'Port29SDKDATA_run-001.json').read_text())
assert run['exit_status'] == 0 and run['lean_charges'] == 0 and run['stopped'] is None
assert run['aggregate_child_peak_rss_bytes'] < run['memory_limit_bytes'] == 512*1024**2
assert not Path(audit['absent_required_rules']).exists(), 'Required rules appeared; review before finalizing blocker'
for p in T.glob('*.py'):
    ast.parse(p.read_text())
paths = subprocess.check_output(['git', 'diff', '--name-only', '7b3ff55fffc'], cwd=R, text=True).splitlines()
paths += subprocess.check_output(['git', 'ls-files', '--others', '--exclude-standard'], cwd=R, text=True).splitlines()
assert all(p.startswith(allowed) for p in paths), paths
files = [p for root in [T,E] for p in root.iterdir() if p.is_file()]
assert all(p.name.startswith('Port29SDKDATA_') and p.stat().st_size <= 5_000_000 for p in files)
assert not any(p.suffix in ['.olean','.o','.ir','.pyc','.a','.so','.dylib'] for p in files)
receipt = dict(status='PASS focused evidence/path consistency; full raw declaration audit BLOCKED',
    command=[sys.executable, '-B', str(Path(__file__).resolve())],
    source_revision=subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=R, text=True).strip(),
    files=[pin(p) for p in sorted(files)], lean_invocations=0,
    budget=dict(global_actual=349, ceiling=368, remaining=19, unused_here=2,
                other_unassigned=5, reserved_actual_consumer=5, former_Port24_carry=7),
    exit_status=0, wall_seconds=time.monotonic()-start, peak_rss_bytes=resource.getrusage(0).ru_maxrss,
    swaps=resource.getrusage(0).ru_nswap, print_axioms='N/A: data-only consistency check',
    python=dict(version=sys.version, executable=pin(Path(sys.executable).resolve())))
with (E / 'Port29SDKDATA_check.json').open('x') as f:
    json.dump(receipt, f, indent=2)
    f.write('\n')
print(json.dumps({k: receipt[k] for k in ['status','exit_status','wall_seconds','peak_rss_bytes','swaps','budget']}))
