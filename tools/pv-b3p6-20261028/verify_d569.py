"""Verify focused receipts, source authorities, NEP completeness and retention."""
from pathlib import Path
import json,hashlib,re,subprocess,collections
R=Path('evidence/pv-b3p6-20261028/resume18');sha=lambda b:hashlib.sha256(b).hexdigest()
inv=json.loads((R/'D569-final-host-inventory.json').read_text())
for n,h in inv['hashes'].items():
 p=R/n.removeprefix('resume18/')
 if n.startswith('source/NEP_'):p=R/'nep-reachable'/Path(n).name
 if '/'not in n:p=R/('D569-'+n)
 assert sha(p.read_bytes())==h,n
rows=[]
for p in sorted(R.glob('lean-797*/receipt/receipt.json')):
 r=json.loads(p.read_text())
 if r['attempt']<79766:continue
 assert r['limits']=={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'}
 assert r['swaps']==0 and r['shared_sources_written']is False
 assert sha((p.parent.parent/'source.lean').read_bytes())==r['source_sha256']
 assert sha(subprocess.check_output(['git','cat-file','blob',r['project_source_authority']['blob']]))==r['source_sha256']
 for name in ['reservation.json','barrier.json']:
  admission=json.loads((p.parent.parent/name).read_text());assert admission['allowed']is True
  for c in admission.get('cgroups',[]):
   path=c.get('path','')
   assert not(c.get('populated')is True and 'pv-b3p6-'in path and f'lean-{r["attempt"]}.'not in path),(r['attempt'],'overlapping scope',path)
 log=(p.parent/'stdout.log').read_text()+(p.parent/'stderr.log').read_text()
 if r['exit_status']==0:
  assert 'error:'not in log and 'sorryAx'not in log and 'native.decide'not in log
  axioms=re.findall(r'depends on axioms:\s*\[(.*?)\]',log,re.S)
  assert all(set(a.replace('\n','').replace(' ','').split(','))<={'propext','Classical.choice','Quot.sound'}for a in axioms)
 rows.append({k:r[k]for k in ['attempt','module','source_sha256','exit_status','wall_seconds','peak_rss_kib','swaps','source_revision','lean_source_revision','print_axioms']})
assert len(rows)==15 and sum(r['exit_status']==0 for r in rows)==13
raw=[]
for a,count in [(79770,2),(79780,10)]:
 log=(R/f'lean-{a}/receipt/stdout.log').read_text();assert 'NEP_FAILURE'not in log
 results=[json.loads(s)for s in re.findall(r'^NEP_RESULT (.*)$',log,re.M)];assert len(results)==count
 for x in results:
  assert x['equal']is True and set(x['walked_axioms'])<={'propext','Classical.choice','Quot.sound'}
 raw.extend(results)
native=[]
for a in [79186,79187,79188,79189]:
 p=R/f'N{a}/receipt/receipt.json';r=json.loads(p.read_text());assert r['swaps']==0
 assert r['limits']=={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'}
 native.append(dict(id=a,**{k:r[k]for k in ['exit_status','wall_seconds','peak_rss_kib','source_revision','swaps']}))
assert [r['exit_status']for r in native]==[0,2,0,0]
assert json.loads((R/'D569-external-verification-resume18.json').read_text())['mismatches']==[]
assert json.loads((R/'D569-cache-verification-resume18.json').read_text())['mismatches']==[]
assert '0 loaded units listed'in inv['scopes']
assert inv['budget']==dict(original_lean_remaining=21,new_906xx_block_remaining=100,extraction_remaining=3,kani_remaining=25)
assert json.loads((R/'FORMATTING-EVENTS-D569.json').read_text())['static_event_counts']=={'builtin index (implicit bounds diagnostic)':451,'MIR assertion':29,'explicit diagnostic/precondition call':43,'direct panic':5}
x=dict(target='NOT ESTABLISHED; DeployedWrapper557 base ops remains OPEN',new_lean_charged=15,lean_success=13,failures=[79766,79773],new_extraction=4,new_kani=0,receipts=rows,native_receipts=native,raw_NEPAudits=raw,raw_scope='complete reachable graphs of the twelve requested roots (two predecessor, ten final); not all unused imports',summary_based_print_axioms='standard only for every successful theorem compile; separate from raw NEP',external_objects=5673,retained_private_objects=867,host_hashes_verified=len(inv['hashes']),peak_lean_rss_kib=max(r['peak_rss_kib']for r in rows),longest_lean_wall_seconds=max(r['wall_seconds']for r in rows),all_swap_zero=True,own_scope_overlap_detected=False,budget=inv['budget'],next_lean=inv['next_lean'],full_frozen_manifest_run=False,premises_removed=[],premises_added=[],premises_weakened=[],checkpoint='context checkpoint, not budget exhaustion')
(R/'verification-summary-D569.json').write_text(json.dumps(x,indent=2)+'\n');print(json.dumps({k:x[k]for k in ['new_lean_charged','lean_success','new_extraction','host_hashes_verified','peak_lean_rss_kib','budget']}))
