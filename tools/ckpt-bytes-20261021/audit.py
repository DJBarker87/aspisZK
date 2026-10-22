#!/usr/bin/env python3
"""Audit focused local receipts; no build or solver replay."""
import hashlib
import json
from pathlib import Path
import re
import subprocess

ROOT = Path(__file__).resolve().parents[2]
PACKET = ROOT / 'docs/research/100bit-spend-path-20261013'
HERE = PACKET / 'evidence/ckpt-bytes-20261021'
BASE = '6f59f538dfb6c8ecb786614d0885594eee45b837'
ALLOWED = {'propext', 'Classical.choice', 'Quot.sound'}

def sha(p):
    return hashlib.sha256(Path(p).read_bytes()).hexdigest()

for pin in json.loads((HERE / 'source-pins.json').read_text())['files']:
    assert sha(ROOT / pin['path']) == pin['sha256'], pin
    assert (ROOT / pin['path']).stat().st_size == pin['size'], pin
for generator in ['generate_sparse.py','generate_sparse_k.py','generate_sparse_digest.py']:
    subprocess.run(['python3','-B',str(ROOT / 'tools/ckpt-bytes-20261021' / generator),'--check'],check=True)
manifest = json.loads((HERE / 'manifest.json').read_text())
accepted = [a for a in manifest['attempts'] if a['final_current']]
modules = sorted(p.stem for p in (PACKET / 'lean').glob('CheckpointBytes*.lean'))
assert sorted(a['module'] for a in accepted) == modules
reports = []
for a in accepted:
    source = PACKET / 'lean' / (a['module'] + '.lean')
    assert a['exit'] == 0 and a['source_unchanged'] and not a['errors']
    assert a['source_sha256'] == sha(source)
    attempt = HERE / (a['module'] + '-' + str(a['attempt']))
    assert sha(attempt / 'source.lean.txt') == sha(source)
    assert json.loads((attempt / 'receipt.json').read_text()) == a
    assert a['peak_rss_bytes'] < 8 * 1024**3 and a['swaps'] == 0
    log = (ROOT / a['log']).read_text()
    extracted = re.findall(r"'[^']+' (?:depends on axioms: \[[\s\S]*?\]|does not depend on any axioms)", log)
    assert extracted == a['axioms']
    for report in a['axioms']:
        if 'depends on axioms:' in report:
            names = {n.strip() for n in report.split('[',1)[1].rsplit(']',1)[0].split(',')}
            assert names <= ALLOWED, report
        reports.append(report)
    for theorem in re.findall(r'^theorem (\w+)',source.read_text(),re.M):
        assert any(r.split("'")[1].endswith('.' + theorem) for r in extracted), theorem
    assert not re.search(r'\b(sorry|axiom|admit|native_decide|bv_decide|maxRecDepth|maxHeartbeats)\b',source.read_text())
    for dep in a['direct_imports']:
        assert sha(dep['path']) == dep['sha256'], dep
    for dep in a['owned_transitive_dependencies']:
        assert sha(ROOT / dep['source']) == dep['source_sha256'], dep
        assert sha(dep['object']) == dep['object_sha256'], dep
changed = subprocess.check_output(['git','diff','--name-only',BASE],cwd=ROOT,text=True).splitlines()
allowed_prefixes = ('tools/ckpt-bytes-20261021/',str(HERE.relative_to(ROOT)) + '/',
                    str((PACKET / 'lean').relative_to(ROOT)) + '/CheckpointBytes')
assert all(p.startswith(allowed_prefixes) for p in changed), changed
for p in HERE.rglob('*'):
    if p.is_file() and p.suffix == '.json':
        assert p.stat().st_size <= 5_000_000
subprocess.run(['git','diff','--check'],cwd=ROOT,check=True)
subprocess.run(['git','diff','--cached','--check'],cwd=ROOT,check=True)
result = {'schema':'checkpoint-bytes-focused-audit-v1','modules':modules,
          'accepted_attempts':len(accepted),'axiom_reports':len(reports),
          'maximum_peak_rss_bytes':max(a['peak_rss_bytes'] for a in accepted),
          'swaps':sum(a['swaps'] for a in accepted),'changed_paths':changed,
          'scope':'focused compatible-cache packet; not a coherent frozen release replay',
          'source_revision':subprocess.check_output(['git','rev-parse','HEAD'],cwd=ROOT,text=True).strip()}
(HERE / 'audit-result.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({k:result[k] for k in ['accepted_attempts','axiom_reports','maximum_peak_rss_bytes','swaps']}))
