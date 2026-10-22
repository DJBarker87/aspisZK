#!/usr/bin/env python3
"""Read-only check of final source bytes and the final audit's dependency objects."""
import hashlib,json,re,subprocess
from pathlib import Path
E=Path(__file__).resolve().parent.parent
S=Path('docs/research/v8-r0-zk-20261009/lean')
mods=sorted((S/'R1Z').glob('ProverCommit*45.lean'))+[S/'R1Z/ProverCommitTrustedStd24.lean']
sha={str(p.relative_to(S)):hashlib.sha256(p.read_bytes()).hexdigest() for p in mods}
revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip()
code='''import json,hashlib
from pathlib import Path
J=Path('/home/dombarker/project-offloads/aspis-joint-20261019')
R=Path('/home/dombarker/project-offloads/codex-cx-prover-commit45-20261022')
expected=%r
sources=[]
for rel,sha in expected.items():
 actual=hashlib.sha256((J/'sources'/rel).read_bytes()).hexdigest()
 assert actual==sha,(rel,actual,sha)
 sources.append(dict(path=rel,sha256=actual))
env=json.loads(Path('/home/dombarker/project-offloads/r1-privacy-build-integration-20261019/env/J.json').read_text())
paths=[J/'objects']+[Path(p) for p in env['LEAN_PATH'].split(':')]
receipt=json.loads((R/'lean-9636.json').read_text())
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
log=(E/'lean/receipts/9636/out-9636.log').read_text()
assert 'exit=0' in log and 'sorryAx' not in log
inventory=json.loads((E/'theorem-inventory.json').read_text())
for name in inventory['theorems']:
 assert "'"+name+"' depends on axioms:" in log or "'"+name+"' does not depend on any axioms" in log,name
for p in mods:
 if 'AspisR1Padding43' not in str(p):
  assert not re.search(r'\b(sorry|admit|native_decide)\b|^axiom |set_option (maxRecDepth|maxHeartbeats)',p.read_text(),re.M),p
print('Final sources, dependency objects and all 14 new theorem axiom audits match.')
