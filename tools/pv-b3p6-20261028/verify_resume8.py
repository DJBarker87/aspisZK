"""Verify all D425 receipts and current-source audit coverage."""
from pathlib import Path
import json,re,hashlib,lzma
D=Path('evidence/pv-b3p6-20261028/resume8');index=json.loads((D/'receipt-index.json').read_text());t=json.loads((D/'TALLY-resume8.json').read_text());native=json.loads((D/'native-receipt-index.json').read_text())
assert len(index)==t['lean_attempts'] and len(index)<=100
assert all(62300<=r['attempt']<=62399 for r in index)
assert len({r['attempt']for r in index})==len(index)
assert sorted(t['used_ids'])==sorted(r['attempt']for r in index)
assert t['audit_ids_used']==[62397,62398,62399]
assert len(native)<=40 and t['native_scopes']==len(native) and t['kani_runs']==0
admission=json.loads((D/'admission-audit.json').read_text());assert admission['errors']==[] and admission['void_attempts']==[]
assert len(admission['refusals'])==len(t['refusals'])
allowed={'propext','Classical.choice','Quot.sound'};bad=[];latest={};peak=[]
axiom_re=r"^'([^'\n]+)' (?:depends on axioms:\s*\[([^\]]*)\]|does not depend on any axioms)"
for row in index+native:
 p=D/row['receipt'];r=json.loads(p.read_text());log=(p.parent/'stdout.log').read_text()+'\n'+(p.parent/'stderr.log').read_text()
 assert r['swaps']==0 and r['limits']['memory.swap.max']=='0'
 assert int(r['limits']['memory.max'])==8*2**30 and int(r['limits']['memory.high'])==6*2**30 and int(r['limits']['pids.max'])==64
 for gate in ['reservation.json','barrier.json']:assert json.loads((p.parent.parent/gate).read_text())['allowed']is True
 if 'module'in row:
  src=p.parent.parent/'source.lean';assert hashlib.sha256(src.read_bytes()).hexdigest()==r['source_sha256']
  if row['exit']==0:
   assert 'sorryAx'not in log,row['attempt']
   for m in re.finditer(axiom_re,log,re.M):
    ax={a.strip()for a in (m[2]or'').split(',')if a.strip()}
    if ax-allowed:bad.append(dict(attempt=row['attempt'],theorem=m[1],axioms=sorted(ax)))
   latest[row['module']]=row
 peak.append(dict(label=row['label'],peak_rss_kib=r['peak_rss_kib'],wall_seconds=r['wall_seconds']))
assert not bad,bad
for module,row in latest.items():
 p=Path('evidence/pv-b3p6-20261028/lean')/(module+'.lean')
 if p.exists():assert hashlib.sha256(p.read_bytes()).hexdigest()==row['source_sha256'],module
expected=json.loads((D/'audit-theorems.json').read_text());audit=next(r for r in index if r['attempt']==62398)
log=(D/audit['receipt']).parent.joinpath('stdout.log').read_text();actual=[m[1]for m in re.finditer(axiom_re,log,re.M)]
assert sorted(actual)==sorted(expected) and len(set(actual))==len(actual)
external=json.loads((D/'external-verification-resume8.json').read_text());assert external['checked_before_any_compile'] and not external['mismatches']
cache=json.loads((D/'cache-verification-resume8.json').read_text());assert not cache['mismatches']
for p in D.rglob('*.sha256'):
 target=Path(str(p)[:-7]+'.xz')
 if target.exists():assert hashlib.sha256(lzma.open(target).read()).hexdigest()==p.read_text().strip(),p
assert not[p for p in D.rglob('*')if p.is_file()and p.stat().st_size>20*1024*1024]
for a in [62397,62398,62399]:assert next(r for r in index if r['attempt']==a)['exit']==0
summary=dict(entry='884adf0f9d0a199263bbeef2fd18cb6881a4b6cf',charged_attempts=len(index),passed=sum(r['exit']==0 for r in index),rejected=sum(r['exit']!=0 for r in index),audit_ids=t['audit_ids_used'],audited_theorems=len(actual),accepted_axioms=sorted(allowed),bad_accepted_axioms=bad,refusals_uncharged=len(admission['refusals']),void_attempts=[],native_scopes=len(native),kani_runs=0,external_objects_verified_before_first_compile=external['checked_count'],retained_objects_verified=cache['checked'],source_snapshots_verified=len(index),latest_objects_with_current_source=len(latest),max_process_rss=max(peak,key=lambda r:r['peak_rss_kib']),all_swap_zero=True,target_established=False,runjoin_op227_discharged=False,full_endpoint_manifest_replayed=False,formatting_classification='DONE in resume7; reused without redoing',semantic_use='reclassification within existing Charon/Aeneas tool trust')
(D/'verification-summary.json').write_text(json.dumps(summary,indent=2)+'\n');print(json.dumps(summary,indent=2))
