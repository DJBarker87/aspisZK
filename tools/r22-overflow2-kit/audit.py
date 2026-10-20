#!/usr/bin/env python3
"""Validate compact evidence without replaying a theorem or full census."""
import hashlib,json,re,subprocess
from pathlib import Path
ROOT=Path(__file__).resolve().parents[2]
OUT=ROOT/'docs/research/100bit-spend-path-20261013/evidence/r22-overflow2-20261021'
sha=lambda b:hashlib.sha256(b).hexdigest()
sources=[*OUT.joinpath('sources').rglob('*'),*Path(__file__).parent.joinpath('generated').glob('*')]
by_sha={sha(p.read_bytes()):p for p in sources if p.is_file()}
rows=[]
for p in sorted(OUT.joinpath('attempts').glob('*/receipt.json')):
    r=json.loads(p.read_text())
    for key in ['module','attempt','source_revision','source_sha256','deps_fingerprint','command','exit_status','wall_seconds','peak_rss_kib','swaps','print_axioms','limits','inputs']:
        assert key in r,(p,key)
    assert r['swaps']==0 and r['print_axioms'].startswith('N/A: Kani')
    assert r['limits']=={'memory.high':str(6*2**30),'memory.max':str(8*2**30),'memory.swap.max':'0','pids.max':'64'}
    assert r['source_sha256']==sha(json.dumps(r['inputs'],sort_keys=True).encode())
    assert r['deps_fingerprint'] in by_sha,(p,'missing source pins')
    for name,h in r['inputs'].items():assert h in by_sha,(p,'missing input',name,h)
    cmd=r['command'];assert '--no-unwinding-assertions' not in cmd and '--no-overflow-checks' not in cmd
    if r['verification_success']:assert r['exit_status']==0
    rows.append(r)
index=json.loads((OUT/'contract-index.json').read_text())
by_attempt={r['attempt']:r for r in rows}
for contract in index['contracts']:
    for proof in contract['proofs']:assert by_attempt[proof]['verification_success'],proof
lean=[]
for p in OUT.joinpath('receipts').glob('*/command.json'):
    r=json.loads(p.read_text());assert all(k in r for k in ['source_revision','source_sha256','deps_fingerprint','wall_s','peak_rss_bytes','process_swaps','axioms','exit'])
    if r['exit']==0:
        assert len(r['axioms'])==4 and all('sorryAx' not in a and all(x in ['propext','Classical.choice','Quot.sound'] for x in re.findall(r'\[([^]]*)\]',a)[-1].split(', ')) for a in r['axioms'])
    lean.append(r)
changed=subprocess.check_output(['git','diff','--name-only','3e55056bf'],cwd=ROOT,text=True).splitlines()
assert all(p.startswith(('tools/r22-overflow2-kit/','docs/research/100bit-spend-path-20261013/evidence/r22-overflow2-20261021/')) or p in ['docs/research/100bit-spend-path-20261013/lean/R22OverflowContinuation2Cadence.lean','docs/research/100bit-spend-path-20261013/design/R22-OVERFLOW-20261021.md'] for p in changed),changed
result=dict(schema='r22-overflow2-audit-v1',kani_attempts=len(rows),successful_kani_attempts=sum(r['verification_success'] for r in rows),lean_attempts=len(lean),successful_lean_attempts=sum(r['exit']==0 for r in lean),successful_new_lean_theorems=4,all_attempt_sources_retained=True,standard_axioms_on_success=True,protected_shipped_sources_and_endpoints_unchanged=True,full_census_replayed=False,scope='Local source-bound function contracts and compositional checks. R22 whole-cone acceptance implication remains open.')
(OUT/'audit.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result))
