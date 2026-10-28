"""Verify/normalize retained receipts without re-running any proof or gate."""
from pathlib import Path
import json,re,hashlib,collections
D=Path('evidence/pv-b3p6-20261028/resume6');index=json.loads((D/'receipt-index.json').read_text());t=json.loads((D/'TALLY-resume6.json').read_text())
assert len(index)==100 and t['lean_attempts']==100 and t['used_ids']==list(range(60800,60900))
assert t['audit_ids_used']==[60897,60898,60899] and t['native_scopes']==0 and t['kani_runs']==0
axiom_re=r"^'([^'\n]+)' (depends on axioms:\s*\[([^\]]*)\]|does not depend on any axioms)"
allowed={'propext','Classical.choice','Quot.sound'};bad=[];latest={};peak=[]
for row in index:
 p=D/row['receipt'];r=json.loads(p.read_text());log=(p.parent/'stdout.log').read_text()+'\n'+(p.parent/'stderr.log').read_text()
 full=[m[0] for m in [(x.group(0),)for x in re.finditer(axiom_re,log,re.M)]]
 r['print_axioms']=full;row['print_axioms']=full
 r['axioms_metadata_note']='Full multiline #print axioms blocks recovered from unchanged stdout/stderr; earlier wrapper regex truncated blocks after one continuation line.'
 p.write_text(json.dumps(r,indent=2)+'\n')
 src=p.parent.parent/'source.lean';assert hashlib.sha256(src.read_bytes()).hexdigest()==r['source_sha256']
 assert r['swaps']==0 and r['limits']['memory.swap.max']=='0'
 assert int(r['limits']['memory.max'])==8*2**30 and int(r['limits']['memory.high'])==6*2**30 and int(r['limits']['pids.max'])==64
 if row['exit']==0:
  assert 'sorryAx'not in log,row['attempt']
  for m in re.finditer(axiom_re,log,re.M):
   ax={a.strip()for a in (m[3]or'').split(',')if a.strip()}
   if ax-allowed:bad.append(dict(attempt=row['attempt'],theorem=m[1],axioms=sorted(ax)))
  latest[row['module']]=row
 peak.append(dict(attempt=row['attempt'],module=row['module'],peak_rss_kib=r['peak_rss_kib'],cgroup_peak=r['cgroup_memory_peak_bytes']))
assert not bad,bad
for module,row in latest.items():
 p=Path('evidence/pv-b3p6-20261028/lean')/(module+'.lean')
 assert p.exists() and hashlib.sha256(p.read_bytes()).hexdigest()==row['source_sha256'],module
expected=set(json.loads((D/'audit-theorems.json').read_text()))
audit=next(r for r in index if r['attempt']==60898);actual={m[1]for m in re.finditer(axiom_re,(D/audit['receipt']).parent.joinpath('stdout.log').read_text(),re.M)}
assert actual==expected,(expected-actual,actual-expected)
external=json.loads((D/'external-verification-resume6.json').read_text());assert external['checked_before_any_compile'] and not external['mismatches']
summary=dict(entry='897c2b28a6265d94da66bf455792a5f73cc66bdc',charged_attempts=100,passed=sum(r['exit']==0 for r in index),rejected=sum(r['exit']!=0 for r in index),audit_ids=t['audit_ids_used'],audited_theorems=len(actual),accepted_axioms=sorted(allowed),bad_accepted_axioms=bad,refusals_uncharged=len(t.get('refusals',[])),native_scopes=0,kani_runs=0,external_objects_verified_before_first_compile=external['checked_count'],source_snapshots_verified=100,latest_objects_with_current_source=len(latest),max_process_rss=max(peak,key=lambda r:r['peak_rss_kib']),max_cgroup_peak=max(peak,key=lambda r:r['cgroup_peak']),all_swap_zero=True,target_established=False,V244='suspended at budget exhaustion; exact residuals in RESIDUALS.md',runjoin_op227_discharged=False,full_endpoint_manifest_replayed=False)
(D/'receipt-index.json').write_text(json.dumps(index,indent=2)+'\n');(D/'verification-summary.json').write_text(json.dumps(summary,indent=2)+'\n')
print(json.dumps(summary,indent=2))
