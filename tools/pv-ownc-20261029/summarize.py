"""Summarize retained receipts without promoting model proofs to row closure."""
from pathlib import Path
import json,re,hashlib,datetime,subprocess
R=Path(__file__).resolve().parents[2];E=R/'evidence/pv-ownc-20261029'
rows=[json.loads(p.read_text()) for p in sorted(E.glob('lean-*/receipt.json'))]
assert len(rows)==100 and sorted(x['attempt'] for x in rows)==list(range(62800,62900))
allowed={'propext','Classical.choice','Quot.sound'};bad=[]
for j in rows:
 if j['exit']!=0:continue
 for a in re.findall(r'depends on axioms:\s*\[([^\]]*)\]',j['print_axioms'],re.S):
  names={x.strip() for x in a.split(',') if x.strip()}
  if not names<=allowed:bad.append(dict(attempt=j['attempt'],axioms=sorted(names)))
assert not bad,bad
manifest=json.loads((E/'frozen-proof-manifest.json').read_text())
axioms=(E/'lean-62898/output.log').read_text()
for root in manifest['roots']:assert "'"+root+"'" in axioms,root
ref=json.loads((E/'lean-62859/refusal-1/admission-launch.json').read_text())
ref_epoch=datetime.datetime.fromisoformat(ref['utc']).timestamp()
starts=[]
for p in list(E.glob('lean-*/receipt.json'))+list(E.glob('native-*/receipt.json')):
 for name in ['admission-before.json','admission-launch.json','admission-barrier.json']:
  a=json.loads((p.parent/name).read_text());assert a['allowed'] is True,(p,name)
 a=json.loads((p.parent/'admission-launch.json').read_text())
 t=datetime.datetime.fromisoformat(a['utc']).timestamp()
 assert t<ref_epoch or t>=ref_epoch+180,(p,t-ref_epoch)
 starts.append(dict(target=p.parent.name,utc=a['utc'],after_refusal_seconds=t-ref_epoch if t>=ref_epoch else None))
report=dict(branch=subprocess.check_output(['git','branch','--show-current'],text=True).strip(),base='55358c233b',source_revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),lean_starts=len(rows),passed=sum(x['exit']==0 for x in rows),failed=[x['attempt'] for x in rows if x['exit']!=0],new_development_modules=len(manifest['modules']),new_development_axioms_queries=len(manifest['roots']),axioms_only=sorted(allowed),bad_axioms=bad,max_lean_rss_kib=max(int(x['peak_rss_kib']) for x in rows),all_lean_swaps_zero=all(int(x['swap'])==0 for x in rows),audits=[x for x in rows if x['attempt']>=62897],native=[json.loads(p.read_text()) for p in sorted(E.glob('native-*/receipt.json'))],admission=dict(actual_starts=starts,all_allowed=True,cooldown_minimum_after_refusal_seconds=min(x['after_refusal_seconds'] for x in starts if x['after_refusal_seconds'] is not None)),row_statuses={x:'SUSPENDED' for x in ['V229','V230','V239','V178 cleanup']},endpoint_premises=dict(removed=0,added=0,changed=0),scope='checked source-stage models; complete own-1 source instance and consumed row composition remain open')
(E/'combined-audit.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps({k:report[k] for k in ['lean_starts','passed','failed','new_development_modules','new_development_axioms_queries','max_lean_rss_kib','all_lean_swaps_zero']}))
for j in report['audits']:print(j['attempt'],j['module'],j['exit'],j['wall'],j['peak_rss_kib'],j['swap'],j['source_revision'])
print('cooldown',report['admission']['cooldown_minimum_after_refusal_seconds'])
