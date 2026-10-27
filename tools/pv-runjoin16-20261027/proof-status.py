"""Classify current proof bytes against successful focused receipts."""
from pathlib import Path
import json,hashlib,subprocess
R=Path(__file__).resolve().parents[2];E=R/'evidence/pv-runjoin16-20261027';L=R/'docs/research/v8-r0-zk-20261009/lean';rows=[]
baseline=set(subprocess.check_output(['git','ls-tree','-r','--name-only','f44d7c5a42','--','docs/research/v8-r0-zk-20261009/lean/R1Z'],cwd=R,text=True).splitlines())
for p in sorted((L/'R1Z').glob('PV_RunJoin_*16*.lean')):
 if str(p.relative_to(R)) in baseline:continue
 module='R1Z/'+p.stem;sha=hashlib.sha256(p.read_bytes()).hexdigest();receipts=[]
 for q in E.glob('receipt-[0-9]*.json'):
  r=json.loads(q.read_text())
  if r['target']==module and r['source_sha256']==sha and r.get('accepted'):receipts.append(r)
 rows.append(dict(module=module,source_sha256=sha,kernel_checked=bool(receipts),successful_attempts=[r['attempt'] for r in receipts]))
(E/'proof-status.json').write_text(json.dumps(rows,indent=2)+'\n')
print(json.dumps(dict(checked=sum(r['kernel_checked'] for r in rows),unverified=sum(not r['kernel_checked'] for r in rows))))
