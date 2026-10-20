#!/usr/bin/env python3
"""Audit focused real-history evidence without repeating Lean compilation."""
import hashlib
import json
from pathlib import Path
import re
import subprocess

root = Path(__file__).resolve().parents[1]
report_dir = root / 'r1p-final'
rows = [json.loads(s) for s in
        (report_dir / 'history-real-attempts-9800-9999.jsonl').read_text().splitlines()]
old = [json.loads(s) for s in
       (report_dir / 'history-attempts-9800-9999.jsonl').read_text().splitlines()]
assert len({r['attempt'] for r in old + rows}) == len(old + rows)
assert all(9800 <= r['attempt'] <= 9999 for r in rows)
assert len({(r['module'], r['source_sha256'], r['deps_fingerprint']) for r in rows}) == len(rows)
assert all(r['env'] == 'J' and r['swaps'] == '0' for r in rows)
allowed = {'propext', 'Classical.choice', 'Quot.sound'}
finals = {}
for r in rows:
    finals[r['module']] = r
artifacts = []
audits_total = 0
for module, r in sorted(finals.items()):
    p = root / 'lean' / (module + '.lean')
    s = p.read_text()
    assert r['exit'] == 0, (module, r['exit'])
    assert hashlib.sha256(p.read_bytes()).hexdigest() == r['source_sha256']
    assert not re.search(r'\b(sorry|admit|native_decide)\b|^\s*axiom\s|set_option\s+(maxRecDepth|maxHeartbeats)', s, re.M)
    audits = re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]", r['output'])
    assert len(audits) == len(re.findall(r'^theorem ', s, re.M))
    assert len(audits) == len(re.findall(r'^#print axioms ', s, re.M))
    for name, axioms in audits:
        assert set(a.strip() for a in axioms.split(',') if a.strip()) <= allowed, (name, axioms)
    audits_total += len(audits)
    imports = re.findall(r'^import (\S+)', s, re.M)
    j = '/home/dombarker/project-offloads/aspis-joint-20261019'
    dep_paths = [line.split(maxsplit=1)[1] for line in r['dependency_objects']]
    # Pin source, compiled object, size, and unchanged direct dependency objects.
    commands = [f'sha256sum {j}/sources/{module}.lean',
                f'sha256sum {j}/objects/{module}.olean',
                f'stat -c %s {j}/objects/{module}.olean']
    commands += ['sha256sum ' + p for p in dep_paths]
    out = subprocess.check_output(['ssh', 'dombarker@100.108.41.90',
                                   'set -e\n' + '\n'.join(commands)], text=True).splitlines()
    assert out[0].split()[0] == r['source_sha256']
    assert out[3:] == r['dependency_objects']
    artifacts.append(dict(module=module, attempt=r['attempt'], source_sha256=r['source_sha256'],
                          source_revision=r['source_revision'], deps_fingerprint=r['deps_fingerprint'],
                          exit=r['exit'], wall=r['wall'], peak_rss_kib=r['peak_rss_kib'], swaps=r['swaps'],
                          audits=audits, object_sha256=out[1].split()[0], object_size=int(out[2])))
# Every pre-existing tracked Lean module is byte-identical to the assigned base.
base = 'de2dd2c8b'
tracked = subprocess.check_output(['git', 'ls-tree', '-r', '--name-only', base,
                                 str(root / 'lean')], text=True).splitlines()
for name in tracked:
    if name.endswith('.lean'):
        expected = subprocess.check_output(['git', 'show', base + ':' + name])
        assert Path(name).read_bytes() == expected, name
# Check the report's literal before/after binder excerpts and obstruction signature.
report = (report_dir / 'PRIVACY-HISTORY-REAL-20261021.md').read_text()
endpoint = (root / 'lean/R1Z/PrivacyR1FinalProtocolHistory.lean').read_text().split(
    'theorem privacy_R1_protocol_history\n', 1)[1]
block = endpoint[endpoint.index('    (realBad :'):endpoint.index('    (R_wire_builder_checker_D75_retry :')]
assert report.count('```lean\n' + block + '```') == 2
obstruction = (root / 'lean/R1Z/QueryScanHistoryRealSpecificationObstruction.lean').read_text()
stmt = obstruction[obstruction.index('theorem no_whole_run_exclusion_with_requested_total'):
                   obstruction.index(' := by\n  intro hh')]
assert '```lean\n' + stmt + '\n```' in report
result = dict(base=base, audited_at_revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),
              attempts=len(rows), modules=len(finals), theorem_audits=audits_total,
              preexisting_lean_modules_unchanged=sum(n.endswith('.lean') for n in tracked),
              artifacts=artifacts)
(report_dir / 'history-real-final-audit.json').write_text(json.dumps(result, indent=2) + '\n')
print(json.dumps({k:v for k,v in result.items() if k != 'artifacts'}, indent=2))
