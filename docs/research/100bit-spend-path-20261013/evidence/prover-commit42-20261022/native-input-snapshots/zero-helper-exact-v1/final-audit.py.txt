#!/usr/bin/env python3
"""Read-only final source/object audit; no builds or regression reruns."""
import hashlib,json,subprocess
from pathlib import Path
E=Path(__file__).resolve().parent.parent
S=Path('docs/research/v8-r0-zk-20261009/lean')
mods=['ProverCommitConditionalRom41','ProverCommitPublicPrefix41','ProverCommitMixedReads41','ProverCommitPublicCoins41','ProverCommitBindingErase41','ProverCommitAudit41']
sha={f'R1Z/{m}.lean':hashlib.sha256((S/'R1Z'/(m+'.lean')).read_bytes()).hexdigest() for m in mods}
revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip()
code='''import json,hashlib
from pathlib import Path
J=Path('/home/dombarker/project-offloads/aspis-joint-20261019')
R=Path('/home/dombarker/project-offloads/codex-cx-prover-commit42-20261022')
expected=%r
sources=[]
for rel,sha in expected.items():
 actual=hashlib.sha256((J/'sources'/rel).read_bytes()).hexdigest()
 assert actual==sha,(rel,actual,sha)
 sources.append(dict(path=rel,sha256=actual))
env=json.loads(Path('/home/dombarker/project-offloads/r1-privacy-build-integration-20261019/env/J.json').read_text())
paths=[J/'objects']+[Path(p) for p in env['LEAN_PATH'].split(':')]
receipt=json.loads((R/'lean-8137.json').read_text())
objects=[]
for m,sha in receipt['deps']:
 rel=Path(m.replace('.','/')).with_suffix('.olean')
 p=next(p/rel for p in paths if (p/rel).exists())
 actual=hashlib.sha256(p.read_bytes()).hexdigest()
 assert actual==sha,(m,actual,sha)
 objects.append(dict(module=m,sha256=actual))
print(json.dumps(dict(source_revision=%r,sources=sources,dependency_objects=objects,all_match=True,compilation_performed=False),indent=2))
'''%(sha,revision)
out=subprocess.check_output(['ssh','dombarker@100.108.41.90','python3 -'],input=code,text=True)
(E/'final-proof-audit.json').write_text(out)
for a in [8136,8137,9189,9195,9197,9198]:
 log=(E/'lean'/'receipts'/str(a)/f'out-{a}.log').read_text()
 assert 'exit=0' in log and 'sorryAx' not in log
for m in mods:
 source=(S/'R1Z'/(m+'.lean')).read_text()
 import re
 assert not re.search(r'\b(sorry|admit|native_decide)\b|^axiom |set_option (maxRecDepth|maxHeartbeats)',source,re.M)
print('Final sources and retained dependency objects match; accepted axioms logs are clean.')
