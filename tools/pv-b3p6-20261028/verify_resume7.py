"""Verify retained D414 receipts, admissions, snapshots, artifact hashes and axioms."""
from pathlib import Path
import json,re,hashlib,lzma,collections
D=Path('evidence/pv-b3p6-20261028/resume7');index=json.loads((D/'receipt-index.json').read_text());t=json.loads((D/'TALLY-resume7.json').read_text());native=json.loads((D/'native-receipt-index.json').read_text())
assert len(index)==100 and t['lean_attempts']==100
assert sorted(t['used_ids'])==list(range(61500,61600))
assert t['audit_ids_used']==[61597,61598,61599]
assert len(native)<=60 and t["native_scopes"]==len(native) and t["kani_runs"]==0
admission=json.loads((D/'admission-audit.json').read_text());assert admission['errors']==[] and admission['void_attempts']==[]
allowed={'propext','Classical.choice','Quot.sound'};bad=[];latest={};peak=[]
for row in index+native:
 p=D/row['receipt'];r=json.loads(p.read_text());log=(p.parent/'stdout.log').read_text()+'\n'+(p.parent/'stderr.log').read_text()
 assert r['swaps']==0 and r['limits']['memory.swap.max']=='0'
 assert int(r['limits']['memory.max'])==8*2**30 and int(r['limits']['memory.high'])==6*2**30 and int(r['limits']['pids.max'])==64
 for gate in ['reservation.json','barrier.json']:assert json.loads((p.parent.parent/gate).read_text())['allowed']is True
 if 'module'in row:
  src=p.parent.parent/'source.lean';assert hashlib.sha256(src.read_bytes()).hexdigest()==r['source_sha256']
  if row['exit']==0:
   assert 'sorryAx'not in log,row['attempt']
   for m in re.finditer(r"^'([^'\n]+)' depends on axioms:\s*\[([^\]]*)\]",log,re.M):
    ax={a.strip()for a in m[2].split(',')if a.strip()}
    if ax-allowed:bad.append(dict(attempt=row['attempt'],theorem=m[1],axioms=sorted(ax)))
   latest[row['module']]=row
 peak.append(dict(label=row['label'],peak_rss_kib=r['peak_rss_kib'],wall_seconds=r['wall_seconds']))
assert not bad,bad
for module,row in latest.items():
 p=Path('evidence/pv-b3p6-20261028/lean')/(module+'.lean')
 assert p.exists() and hashlib.sha256(p.read_bytes()).hexdigest()==row['source_sha256'],module
external=json.loads((D/'external-verification-resume7.json').read_text());assert external['checked_before_any_compile'] and not external['mismatches']
for p in D.rglob('*.sha256'):
 target=Path(str(p)[:-7]+'.xz')
 if not target.exists():continue
 actual=hashlib.sha256(lzma.open(target).read()).hexdigest();assert actual==p.read_text().strip(),p
assert not list(p for p in D.rglob('*')if p.is_file()and p.stat().st_size>20*1024*1024)
for a in [61597,61598,61599]:assert next(r for r in index if r['attempt']==a)['exit']==0
summary=dict(entry='1b86d5a589e710a7c48c726c27392aa200e72223',charged_attempts=100,passed=sum(r['exit']==0 for r in index),rejected=sum(r['exit']!=0 for r in index),audit_ids=t['audit_ids_used'],accepted_axioms=sorted(allowed),bad_accepted_axioms=bad,refusals_uncharged=len(admission['refusals']),void_attempts=[],native_scopes=len(native),kani_runs=0,external_objects_verified_before_first_compile=external['checked_count'],source_snapshots_verified=100,latest_objects_with_current_source=len(latest),max_process_rss=max(peak,key=lambda r:r['peak_rss_kib']),all_swap_zero=True,target_established=False,runjoin_op227_discharged=False,full_endpoint_manifest_replayed=False,formatting_classification='listed generic Write glue unreachable from op227; observed native formatting calls panic-only; constant guards and fixed7/7 dot lengths exclude these panic branches on honest runs under existing compiler/tool boundary; D348 remains open')
(D/'verification-summary.json').write_text(json.dumps(summary,indent=2)+'\n');print(json.dumps(summary,indent=2))
