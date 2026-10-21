#!/usr/bin/env python3
"""Read-only focused receipt/scope audit; --write saves its JSON result."""
import hashlib
import json
from pathlib import Path
import re
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[2]
PACKET = ROOT / 'docs/research/100bit-spend-path-20261013'
EVIDENCE = PACKET / 'evidence/s7-join-20261021'
def sha(p):
    return hashlib.sha256(Path(p).read_bytes()).hexdigest()
manifest = json.loads((EVIDENCE / 'manifest.json').read_text())
accepted = []
allowed = {'propext','Classical.choice','Quot.sound'}
for source in sorted((PACKET / 'lean').glob('S7Join*.lean')):
    body = source.read_text()
    assert not re.search(r'\b(sorry|admit|native_decide)\b|^\s*axiom\s|set_option\s+(maxRecDepth|maxHeartbeats)', body, re.M), source
    matches = [a for a in manifest['attempts'] if a['module']==source.stem and
               a['source_sha256']==sha(source) and a['exit']==0]
    assert matches, 'No successful current-source receipt: '+source.stem
    a = matches[-1]
    directory = EVIDENCE / f"{a['module']}-{a['attempt']}"
    assert sha(directory / 'source.lean.txt')==sha(source)
    assert json.loads((directory / 'receipt.json').read_text())==a
    for dep in a['direct_imports']:
        assert sha(dep['path'])==dep['sha256'], 'Changed cached dependency: '+dep['module']
    for line in a['axioms']:
        names = re.search(r'axioms:\s*\[([\s\S]*?)\]',line)
        if names:
            assert {s.strip() for s in names[1].split(',')}<=allowed, line
        else:
            assert 'does not depend on any axioms' in line,line
    expected = re.findall(r'^#print axioms (\S+)',body,re.M)
    actual = [re.search(r"'([^']+)'",line)[1] for line in a['axioms']]
    for name in expected:
        assert any(n==name or n.endswith('.'+name) for n in actual),(source,name)
    declared = re.findall(r'^(?:private )?(?:theorem|lemma) (\w+)',body,re.M)
    assert set(declared)<=set(expected),(source,'missing theorem axiom audit')
    for field in ['source_revision','exit','wall_seconds','peak_rss_bytes','swaps','deps_fingerprint']:
        assert field in a,(source,field)
    assert a['swaps']==0
    accepted.append({k:a[k] for k in ['module','attempt','source_sha256','source_revision',
        'deps_fingerprint','exit','wall_seconds','peak_rss_bytes','swaps','axioms']})
changed = subprocess.check_output(['git','diff','--name-only','6c520f134'],cwd=ROOT,text=True).splitlines()
for name in changed:
    assert (name.startswith('tools/s7-join-20261021/') or
            name.startswith('docs/research/100bit-spend-path-20261013/evidence/s7-join-20261021/') or
            re.fullmatch(r'docs/research/100bit-spend-path-20261013/lean/S7Join\w+\.lean',name) or
            name=='docs/research/100bit-spend-path-20261013/design/CONE-AUDIT-20261021.md'), name
r17 = PACKET / 'evidence/r17-geometry-20261021/rust/receipt-1.json'
r17receipt = json.loads(r17.read_text())
for path,pin in r17receipt['source_pins'].items():
    assert sha(ROOT/path)==pin, 'R17 reused evidence input changed: '+path
interrupted = [str(p.relative_to(ROOT)) for p in sorted(EVIDENCE.glob('*/command.json'))
               if not (p.parent/'receipt.json').exists()]
result = {'schema':'s7-join-focused-audit-v1','source_revision':subprocess.check_output(
    ['git','rev-parse','HEAD'],cwd=ROOT,text=True).strip(),'formal_release':False,
    'status':'checked additive reference/local execution results; frozen source whole-cone join remains open',
    'accepted':accepted,'axiom_reports':sum(len(a['axioms']) for a in accepted),
    'peak_rss_bytes':max(a['peak_rss_bytes'] for a in accepted),
    'swaps':0,'interrupted_unaccepted_attempts':interrupted,
    'reused_r17_receipt':str(r17.relative_to(ROOT)), 'reused_r17_receipt_sha256':sha(r17),
    'shipped_source_changes':False,'full_frozen_release_replay':False,'premises_deleted':0}
if '--write' in sys.argv:
    (EVIDENCE/'audit-result.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({k:v for k,v in result.items() if k!='accepted'},indent=2))
