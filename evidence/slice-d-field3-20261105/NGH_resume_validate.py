"""Additive receipt validation; no source output and no promotion of failed gates."""
from pathlib import Path
import json,hashlib,re,sys
sys.dont_write_bytecode=True
E=Path(__file__).resolve().parent
J=lambda p:json.loads(p.read_text())
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
rows=[json.loads(l)for l in (E/'NGH_ATTEMPTS.jsonl').read_text().splitlines()]
assert len({r['attempt']for r in rows})==len(rows)
limits={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'}
classified=[]
for r in rows:
 a=r['attempt'];n=int(a[-3:])
 if not ((a.startswith('NGH_K')and n>=45)or(a.startswith('NGH_L')and n>=20)):continue
 assert J(E/a/'receipt.json')==r
 ad=J(E/(a+'-admission.json'));assert ad['exit']==0 and ad['reservation']['allowed']is True
 assert r['limits']==limits and int(r['swaps'])==0
 for p,h in r['source_hashes'].items():assert sha(E/a/'sources'/p)==h,(a,p)
 log=(E/a/'stdout.log').read_text();status='compile/check failure'
 if r['kind']=='kani':
  assert J(E/(a+'-graph-check.json'))['graph_matches_frozen']
  assert not J(E/(a+'-source-check.json'))['errors']
  lock=J(E/(a+'-lock-check.json'));assert lock['unchanged']and lock['before']==lock['after']=='5782e6a32026fdd95d252d0db7ea20b16716e6deb4f5a397e744886bb6ba22ef'
  assert r['env']['CARGO_NET_OFFLINE']=='true'and r['env']['CARGO_PROFILE_DEV_OPT_LEVEL']=='3'
  assert next(p['features']for p in J(E/(a+'-graph-check.json'))['selected_closure']if p['name']=='aspis-core')==['r0']
  if 'timed out'in log.lower():status='solver timeout; no credit'
  elif r['exit_status']==0:
   assert 'VERIFICATION:- SUCCESSFUL'in log;status='native support pass; no composed helper credit'
  elif 'VERIFICATION:- FAILED'in log:status='failed verification; control credit requires matched positive'
 elif r['kind']=='lean'and r['exit_status']==0:
  assert 'sorryAx'not in log
  for line in r['print_axioms']:
   if 'depends on axioms:'in line:assert set(re.search(r'\[([^]]*)\]',line)[1].split(', '))<={'propext','Classical.choice','Quot.sound'}
  status='checked Lean model support'
 classified.append({k:r[k]for k in ['attempt','kind','module','exit_status','wall_seconds','peak_rss_kib','swaps']}|dict(classification=status))
if (E/'NGH_K057/receipt.json').exists():
 import importlib.util
 spec=importlib.util.spec_from_file_location('NGH_resume_native',E/'NGH_validate_native.py');native=importlib.util.module_from_spec(spec);spec.loader.exec_module(native)
 native.copy_pair(56,57)
counts={k:sum(r['kind']==k for r in rows)for k in sorted({r['kind']for r in rows})}
k=sum(r['kind']=='kani'for r in rows);l=sum(r['attempt'].startswith('NGH_L')for r in rows);ex=sum(r['kind']=='extract'for r in rows)
assert k<=60 and l<=60 and ex<=1
assert J(E/'NGH_CELL_STOP.json')['native_credit']is False
closed=J(E/'NGH_CLOSED.json');assert closed['new_composed_rows']==3 and all(x['row']not in ['TX1:032','TX2:022','TX1:056']for x in closed['open_candidates'])
out=dict(status='PASS',kind_counts=counts,charged_budget=dict(kani=k,lean_support=l,extraction=ex),remaining=dict(kani=60-k,lean_support=60-l,extraction=1-ex),new_helper_closures=0,all_new_receipts_frozen_admitted_and_capped=True,attempts=classified)
(E/'NGH_RESUME_VALIDATION.json').write_text(json.dumps(out,indent=1)+'\n')
print(json.dumps({k:out[k]for k in ['status','charged_budget','remaining','new_helper_closures']}))
