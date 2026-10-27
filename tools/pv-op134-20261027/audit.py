"""Audit receipts without rerunning any unchanged proof."""
from pathlib import Path
import json,hashlib,re,subprocess
root=Path(__file__).resolve().parents[2];out=root/'evidence/pv-op134-20261027';lean=root/'docs/research/v8-r0-zk-20261009/lean/R1Z'
tally=json.loads((out/'TALLY.json').read_text())
receipts=[json.loads(p.read_text()) for p in sorted(out.glob('50[0-9][0-9][0-9].json'))]
assert [r['attempt'] for r in receipts]==sorted(tally['lean_charged'])
assert len(receipts)<=100 and len(tally['kani_charged'])<=4
assert len(set(tally['used_ids']))==len(tally['used_ids'])
assert all(50000<=i<=50299 for i in tally['used_ids'])
passed={r['module']:r for r in receipts if r['exit']==0}
standard={'propext','Classical.choice','Quot.sound'}
for r in receipts:
 a=r['attempt'];log=(out/f'out-{a}.log').read_text()
 assert int(re.search(r'^exit=(\d+)',log,re.M)[1])==r['exit']
 assert hashlib.sha256((out/f'{a}-source.lean.txt').read_bytes()).hexdigest()==r['source_sha256']
 assert r['wall'] is not None and r['peak_rss_kib'] is not None and r['swap'] is not None
 if r['exit']==0:
  assert r['swap']=='0'
  assert r['axioms'],(a,'missing axiom audit')
  for names in re.findall(r'depends on axioms: \[([^\]]*)\]',log,re.S):
   assert set(x.strip() for x in names.split(','))<=standard,(a,names)
modules=[]
for p in sorted(lean.glob('PV_Op134_*.lean')):
 sha=hashlib.sha256(p.read_bytes()).hexdigest();name='R1Z/'+p.stem;r=passed.get(name)
 green=bool(r and r['source_sha256']==sha)
 modules.append(dict(module=name,path=str(p.relative_to(root)),sha256=sha,checked=green,receipt=r['attempt'] if green else None))
report=dict(revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),charged=len(receipts),successful_runs=sum(r['exit']==0 for r in receipts),failed_runs=[r['attempt'] for r in receipts if r['exit']!=0],used_ids=tally['used_ids'],kani_charged=tally['kani_charged'],next_id=tally['next_id'],reserved_audit_ids=tally['reserved_audit_ids'],max_rss_kib=max(int(r['peak_rss_kib']) for r in receipts),max_successful_rss_kib=max(int(r['peak_rss_kib']) for r in receipts if r['exit']==0),all_successful_axioms_standard=True,all_successful_swap_zero=True,modules=modules,unchecked=[m['module'] for m in modules if not m['checked']],scope='Focused replay of new modules over restored private overlay; not a deployment-closure release replay.')
(out/'AUDIT.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps({k:v for k,v in report.items() if k not in ['modules','used_ids','unchecked']},indent=2));print('UNCHECKED',len(report['unchecked']))
