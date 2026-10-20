#!/usr/bin/env python3
"""Retain exact failed and accepted source text, never compiled objects."""
import hashlib,json,subprocess
from pathlib import Path
E=Path(__file__).resolve().parent.parent
receipts=sorted((E/'lean').glob('lean-*.json'))
wanted={json.loads(p.read_text())['source_sha256'] for p in receipts}
code='''import hashlib,json
from pathlib import Path
R=Path('/home/dombarker/project-offloads/codex-cx-prover-commit6-20261021')
J=Path('/home/dombarker/project-offloads/aspis-joint-20261019/sources/R1Z')
wanted=set(%r)
found={}
paths=list((R/'snapshots').rglob('*.lean'))+list(J.glob('ProverCommit*.lean'))+[J/'PrivacyR1FinalProtocolQuotient.lean']
for p in paths:
 b=p.read_bytes();h=hashlib.sha256(b).hexdigest()
 if h in wanted:found[h]=dict(path=str(p),text=b.decode())
print(json.dumps(found))
'''%sorted(wanted)
found=json.loads(subprocess.check_output(['ssh','dombarker@100.108.41.90','python3 -'],input=code,text=True))
assert wanted<=found.keys(),wanted-found.keys()
dest=E/'lean/sources';dest.mkdir(exist_ok=True)
index=[]
for p in receipts:
 r=json.loads(p.read_text());h=r['source_sha256'];rec=found[h]
 name=f"attempt-{r['attempt']}-{Path(r['module']).stem}.lean.txt"
 b=rec['text'].encode();assert hashlib.sha256(b).hexdigest()==h
 (dest/name).write_bytes(b)
 index.append(dict(attempt=r['attempt'],file=name,sha256=h,remote_snapshot=rec['path']))
(E/'lean/source-index.json').write_text(json.dumps(index,indent=2)+'\n')
print(json.dumps(dict(attempts=len(index),unique_sources=len(wanted))))
