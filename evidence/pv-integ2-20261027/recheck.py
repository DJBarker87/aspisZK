from pathlib import Path
import json,subprocess,sys
E=Path(__file__).resolve().parent;R=E.parents[1];queue=json.loads((E/'recheck-order.json').read_text());fail=set();records=[]
for row in queue:
 n=row['module'];prior=[]
 for p in (E/'lean-receipts').glob('*/receipt.json'):
  x=json.loads(p.read_text())
  if x['module']==n:prior.append(x)
 if prior:
  if prior[-1]['exit']!=0:fail.add(n)
  continue
 if any(m in fail for m in row['imports']):
  fail.add(n);records.append(dict(module=n,status='blocked by failed unchanged dependency'));continue
 tally=json.loads((E/'TALLY.json').read_text());a=tally['next_unused_id'];assert a<54597
 r=subprocess.run([sys.executable,str(E/'compile-one.py'),str(a),n,str(R/row['path'])])
 if r.returncode==78:sys.exit(78)
 if r.returncode:fail.add(n)
(E/'recheck-blocked.json').write_text(json.dumps(records,indent=2)+'\n')
print('focused queue complete; failed or blocked',sorted(fail),flush=True)
sys.exit(bool(fail))
