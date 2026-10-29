"""Receipt and boundary summary; does not launch any build."""
from pathlib import Path
import json,subprocess,hashlib,re
R=Path(__file__).resolve().parents[2];E=R/'evidence/pv-rjn-20261029';base='c8fb38ee734a84e8cdb4a3f8b8de697fd66195e7'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
rs=[json.loads(p.read_text()) for p in sorted(E.glob('receipt-*.json'))];ms=[v for p in sorted(E.glob('modules-*.json')) for v in json.loads(p.read_text())]
assert len(rs)==len(ms)<=100
assert all(69500<=v['attempt']<=69599 for v in rs)
assert len({v['attempt'] for v in rs})==len(rs)
assert all(v['reservation']['allowed'] is True and v['admission_exit']==0 and v['admission_and_launch_same_shell'] and v['cooldown_checked_before_launch'] for v in rs)
old_failed={v['source_sha256'] for v in json.loads((E/'historical-failures.json').read_text())}
for p in sorted(E.glob('modules-*.json')):
 for v in json.loads(p.read_text()):
  assert v['source_sha256'] not in old_failed,'unchanged failed source'
  if not v['accepted']:old_failed.add(v['source_sha256'])
accepted=[v for v in ms if v['accepted']]
for v in accepted:
 assert not any(x in a for a in v['axioms'] for x in ['sorryAx','admit'])
 for line in v['axioms']:
  if 'depends on axioms:' in line:
   xs=re.search(r'\[(.*?)\]',line,re.S)[1].replace('\n','').split(',')
   assert set(x.strip() for x in xs)<= {'propext','Classical.choice','Quot.sound'}
changes=subprocess.check_output(['git','diff','--name-only',base,'HEAD'],text=True).splitlines()
assert all(p.startswith(('tools/pv-rjn-20261029/','evidence/pv-rjn-20261029/','docs/research/v8-r0-zk-20261009/lean/R1Z/PV_RJN_')) for p in changes),changes
summary=dict(base=base,source_revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),branch=subprocess.check_output(['git','branch','--show-current'],text=True).strip(),attempts=len(rs),accepted=len(accepted),rejected=len(ms)-len(accepted),Kani=0,ids=[v['attempt'] for v in rs],wall_seconds=sum(v['host_wall_seconds'] for v in rs),peak_rss_bytes=max((v['peak_rss_bytes'] for v in rs),default=0),swaps=sum(v['swaps'] for v in rs),void_launches=0,refusals=[dict(path=p.name,**json.loads(p.read_text())) for p in sorted(E.glob('refusal-*.json'))],failed_hash_guard_sha256=sha(R/'tools/pv-rjn-20261029/compile.py'),changes=changes)
(E/'SUMMARY.json').write_text(json.dumps(summary,indent=2)+'\n')
(E/'commits.txt').write_text(subprocess.check_output(['git','log','--oneline',base+'..HEAD'],text=True))
print({k:summary[k] for k in ['attempts','accepted','rejected','Kani','peak_rss_bytes','swaps','void_launches','failed_hash_guard_sha256']})
