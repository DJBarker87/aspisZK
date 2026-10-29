"""Verify exact source snapshots, audit axioms, limits, and unchanged boundaries."""
from pathlib import Path
import json,hashlib,re,subprocess
D=Path('evidence/pv-b3p6-20261028');O=D/'resume10';L=D/'lean';base='9e271d32e606772fffbddf687a4c5deae0eb9c80'
rows=json.loads((O/'receipt-index.json').read_text());t=json.loads((O/'TALLY-resume10.json').read_text());m=json.loads((O/'focused-manifest.json').read_text())
assert len(rows)==t['lean_attempts']==100
assert sorted(r['attempt']for r in rows)==sorted(t['used_ids'])==list(range(64000,64100))
assert t['audit_ids_used']==[64097,64098,64099]
a=json.loads((O/'admission-audit.json').read_text());assert a['errors']==[] and a['void_attempts']==[]
allowed={'propext','Classical.choice','Quot.sound'};pattern=r"^'([^'\n]+)' (?:depends on axioms:\s*\[([^\]]*)\]|does not depend on any axioms)"
for row in rows:
 p=O/row['receipt'];r=json.loads(p.read_text());assert r['exit_status']==row['exit'] and r['swaps']==0
 assert r['limits']=={'memory.high':str(6*2**30),'memory.max':str(8*2**30),'memory.swap.max':'0','pids.max':'64'}
 assert r['command'][-1]=='7000'
 for gate in ['reservation.json','barrier.json']:assert json.loads((p.parent.parent/gate).read_text())['allowed']is True
 raw=(p.parent.parent/'source.lean').read_bytes();assert hashlib.sha256(raw).hexdigest()==r['source_sha256']==row['source_sha256']
 assert subprocess.check_output(['git','show',r['lean_source_revision']+':'+str(L/(r['module']+'.lean'))])==raw
 if row['exit']==0:
  log=(p.parent/'stdout.log').read_text()+'\n'+(p.parent/'stderr.log').read_text();assert 'sorryAx'not in log
  for v in re.finditer(pattern,log,re.M):assert {x.strip()for x in(v[2]or'').split(',')if x.strip()}<=allowed
for s in m['sources']:assert hashlib.sha256(Path(s['path']).read_bytes()).hexdigest()==s['sha256']
for row in rows:
 if row['attempt']>=64097:assert row['exit']==0
axioms=next(r for r in rows if r['attempt']==64098);log=(O/axioms['receipt']).parent.joinpath('stdout.log').read_text();actual=[v[1]for v in re.finditer(pattern,log,re.M)]
assert sorted(actual)==sorted(m['new_theorems']) and len(actual)==len(set(actual))
external=json.loads((O/'external-verification-resume10.json').read_text());cache=json.loads((O/'cache-verification-resume10.json').read_text())
assert external['checked_before_any_compile']and external['mismatches']==[]and cache['mismatches']==[]
assert subprocess.check_output(['git','diff','--name-only',base,'HEAD','--','crates','programs'])==b''
# Recheck the exact four source/reference pairs used in structural association.
inventory=json.loads((D/'resume9/body-inventory.json').read_text());checked=[]
for record in inventory['files']:
 for key in ['source','owned']:
  p=Path(record[key]);h=hashlib.sha256(p.read_bytes()).hexdigest();assert h==record[key+'_sha256'];checked.append(dict(path=str(p),sha256=h))
runjoin=json.loads((O/'runjoin-status.json').read_text());assert runjoin['discharged']is False and runjoin['replacement_theorem']is None
hyp=(O/'runjoin-hypothesis.txt').read_text().rstrip('\n');assert hyp==runjoin['hypothesis']and hashlib.sha256(hyp.encode()).hexdigest()==runjoin['hypothesis_sha256']
summary=dict(charged_attempts=100,passed=sum(r['exit']==0 for r in rows),rejected=sum(r['exit']!=0 for r in rows),audit_ids=t['audit_ids_used'],audited_theorems=len(actual),accepted_axioms=sorted(allowed),source_snapshots_verified=100,source_revision_blobs_verified=100,external_objects_verified_before_first_compile=external['checked_count'],retained_objects_verified=cache['checked_count'],source_reference_files_rechecked=checked,all_swap_zero=True,max_process_rss=max(rows,key=lambda r:r['peak_rss_kib']),refusals_uncharged=len(a['refusals']),void_attempts=[],native_scopes=0,kani_runs=0,runjoin_op227_discharged=False,target_established=False,privacy_premises_removed=[],privacy_premises_added=[],privacy_premises_weakened=[],full_endpoint_manifest_replayed=False,semantic_use='reclassification within existing Charon/Aeneas tool trust',compiler_boundary='V370 / pending owner D381,D386 retained; own-1 source-to-machine boundary, not T')
(O/'verification-summary.json').write_text(json.dumps(summary,indent=2)+'\n');print(json.dumps(summary,indent=2))
