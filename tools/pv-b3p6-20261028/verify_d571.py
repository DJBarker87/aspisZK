"""Verify this continuation's source/receipt chain and NEP completeness."""
from pathlib import Path
import json,hashlib,re,subprocess
D=Path('evidence/pv-b3p6-20261028');R=D/'resume18';sha=lambda b:hashlib.sha256(b).hexdigest()
inv=json.loads((R/'D571-final-host-inventory.json').read_text())
for n,h in inv['hashes'].items():
 p=R/n.removeprefix('resume18/')
 if n.startswith('source/NEP_'):p=R/'nep-reachable'/Path(n).name
 if '/'not in n:p=R/('D571-'+n)
 assert sha(p.read_bytes())==h,n
receipts=[]
for attempt in [79783,79784,79785,79787,79788,79789,79790,79791]:
 p=R/f'lean-{attempt}/receipt/receipt.json';r=json.loads(p.read_text())
 assert r['attempt']==attempt and r['swaps']==0
 assert r['limits']=={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'}
 assert sha((p.parent.parent/'source.lean').read_bytes())==r['source_sha256']
 assert sha(subprocess.check_output(['git','cat-file','blob',r['project_source_authority']['blob']]))==r['source_sha256']
 assert r['shared_sources_written']is False
 for name in ['reservation.json','barrier.json']:
  a=json.loads((p.parent.parent/name).read_text());assert a['allowed']is True
  for c in a.get('cgroups',[]):
   path=c.get('path','')
   assert not(c.get('populated')is True and 'pv-b3p6-'in path and f'lean-{attempt}.'not in path),(attempt,'own overlap',path)
 log=(p.parent/'stdout.log').read_text()+(p.parent/'stderr.log').read_text()
 if r['exit_status']==0:
  assert 'error:'not in log and 'sorryAx'not in log and 'native.decide'not in log
  for a in re.findall(r'depends on axioms:\s*\[(.*?)\]',log,re.S):assert set(a.replace('\n','').replace(' ','').split(','))<={'propext','Classical.choice','Quot.sound'}
 else:assert attempt==79784 and 'Application type mismatch'in log
 receipts.append(r)
assert len(receipts)==8 and sum(r['exit_status']==0 for r in receipts)==7
# The replacement of the failed family changed source, not just its name.
assert receipts[1]['module']==receipts[4]['module']and receipts[1]['source_sha256']!=receipts[4]['source_sha256']
log=(R/'lean-79791/receipt/stdout.log').read_text();raw=[json.loads(s)for s in re.findall(r'^NEP_RESULT (.*)$',log,re.M)]
assert len(raw)==23 and 'NEP_FAILURE'not in log
for x in raw:assert x['equal']is True and set(x['walked_axioms'])<={'propext','Classical.choice','Quot.sound'}
for name in ['external','cache']:
 x=json.loads((R/f'D571-{name}-verification-resume18.json').read_text());assert x['mismatches']==[]
assert '0 loaded units listed'in inv['scopes']
# Source gate and family manifests are deterministic and consume committed input.
for tool in ['pattern_groups571.py','disabled_gates571.py','controlflow_assert571.py']:
 subprocess.run(['python3',f'tools/pv-b3p6-20261028/{tool}','--check'],check=True,stdout=subprocess.PIPE)
counts=json.loads((R/'PANIC-PATTERN-GROUPS-D571.json').read_text())['counts'];assert sum(counts.values())==528
assert inv['budget']==dict(lean_units_remaining=113,extraction_remaining=3,kani_remaining=25)
# NEP driver remains the same private-import/hard-error driver with arrays and label adapted.
s=(D/'lean/PV_B3P_NEPCohort569227.lean').read_text();t=(D/'lean/PV_B3P_NEPCohort571227.lean').read_text()
mask=lambda s:re.sub(r'  let modules :=.*?  let env ←','  let env ←',s,flags=re.S).replace('b3p6_cohort569','b3p6_cohort571')
assert mask(s)==mask(t)
walker=(D/'lean/PV_B3P_NEPWalker569227.lean').read_bytes();provenance=json.loads((R/'NEP-PROVENANCE-D569.json').read_text());assert sha(walker)==provenance['walker_sha256']
x=dict(status='CONTEXT CHECKPOINT; whole-source guards and DeployedWrapper557 remain OPEN',new_lean_charged=8,success=7,failed=[79784],refusals=[79781,79782],prelaunch_retired_id=79786,prelaunch_failure='source authority staging before source commit completed; corrected authority, no compiler ran',new_extraction=0,new_kani=0,host_hashes_verified=len(inv['hashes']),peak_rss_kib=max(r['peak_rss_kib']for r in receipts),longest_wall_seconds=max(r['wall_seconds']for r in receipts),zero_swap=True,raw_NEP_roots=raw,raw_audit_scope='23 complete requested reachable root graphs, including unchanged conditional callback and source cone; not every unused imported declaration',summary_print_axioms_label='SUMMARY-BASED; successful outputs standard-only',pattern_counts=counts,guard_sha256=inv['guard_sha256'],budget=inv['budget'],next_lean=inv['next_lean'],full_frozen_manifest_run=False,premises_removed=[],premises_added=[],premises_weakened=[],receipts=[{k:r[k]for k in ['attempt','module','source_sha256','exit_status','wall_seconds','peak_rss_kib','swaps','source_revision','lean_source_revision','print_axioms']}for r in receipts])
(R/'verification-summary-D571.json').write_text(json.dumps(x,indent=2)+'\n');print(json.dumps({k:x[k]for k in ['new_lean_charged','success','failed','raw_audit_scope','peak_rss_kib','budget','next_lean']}))
