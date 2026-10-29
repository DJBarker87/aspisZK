"""Verify exact source snapshots, audit axioms, limits, and unchanged boundaries."""
from pathlib import Path
import json,hashlib,re,subprocess
D=Path('evidence/pv-b3p6-20261028');O=D/'resume13';L=D/'lean';base='7eab3fb68fe64bacff8e32d371126f5aa75cd865'
rows=json.loads((O/'receipt-index.json').read_text());t=json.loads((O/'TALLY-resume13.json').read_text());m=json.loads((O/'focused-manifest.json').read_text())
assert len(rows)==t['lean_attempts']==100
assert sorted(r['attempt']for r in rows)==sorted(t['used_ids'])==list(range(66600,66700))
assert t['audit_ids_used']==[66697,66698,66699]
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
 if row['attempt']>=66697:assert row['exit']==0
axioms=next(r for r in rows if r['attempt']==66698);log=(O/axioms['receipt']).parent.joinpath('stdout.log').read_text();actual=[v[1]for v in re.finditer(pattern,log,re.M)]
assert sorted(actual)==sorted(m['new_theorems']) and len(actual)==len(set(actual))
external=json.loads((O/'external-verification-resume13.json').read_text());cache=json.loads((O/'cache-verification-resume13.json').read_text())
assert external['checked_before_any_compile']and external['mismatches']==[]and cache['mismatches']==[]
assert subprocess.check_output(['git','diff','--name-only',base,'HEAD','--','crates','programs'])==b''
# Recheck the exact four source/reference pairs used in structural association.
inventory=json.loads((D/'resume9/body-inventory.json').read_text());checked=[]
for record in inventory['files']:
 for key in ['source','owned']:
  p=Path(record[key]);h=hashlib.sha256(p.read_bytes()).hexdigest();assert h==record[key+'_sha256'];checked.append(dict(path=str(p),sha256=h))
runjoin=json.loads((O/'runjoin-status.json').read_text());assert runjoin['discharged']is False and runjoin['replacement_theorem']is None
hyp=(O/'runjoin-hypothesis.txt').read_text().rstrip('\n');assert hyp==runjoin['hypothesis']and hashlib.sha256(hyp.encode()).hexdigest()==runjoin['hypothesis_sha256']
summary=dict(charged_attempts=100,passed=sum(r['exit']==0 for r in rows),rejected=sum(r['exit']!=0 for r in rows),audit_ids=t['audit_ids_used'],audited_theorems=len(actual),accepted_axioms=sorted(allowed),source_snapshots_verified=100,source_revision_blobs_verified=100,external_objects_verified_before_first_compile=external['checked_count'],retained_objects_verified=cache['checked_count'],source_reference_files_rechecked=checked,all_swap_zero=True,max_process_rss=max(rows,key=lambda r:r['peak_rss_kib']),refusals_uncharged=len(a['refusals']),void_attempts=[],native_scopes=30,kani_runs=0,runjoin_op227_discharged=False,target_established=False,privacy_premises_removed=[],privacy_premises_added=[],privacy_premises_weakened=[],full_endpoint_manifest_replayed=False,semantic_use='reclassification within existing Charon/Aeneas tool trust',compiler_boundary='V370 / pending owner D381,D386 retained; own-1 source-to-machine boundary, not T')
(O/'verification-summary.json').write_text(json.dumps(summary,indent=2)+'\n');print(json.dumps(summary,indent=2))

# No dependency or environment change can license unchanged failed source.
failed=set()
for row in sorted(rows,key=lambda r:r['attempt']):
 assert row['source_sha256']not in failed,('unchanged failed source',row['attempt'])
 if row['exit']!=0:failed.add(row['source_sha256'])
native=json.loads((O/'native-receipt-index.json').read_text());assert len(native)==30
codes={
 'missing227-resume13-bytes-charon':101,
 'missing227-resume13-equality-aeneas':2,
 'missing227-resume13-safe-equality-aeneas':2,
 'missing227-resume13-public-aeneas':2,
 'missing227-resume13-publicbytes-aeneas':2,
 'missing227-resume13-semantic-root13-aeneas':2,
 'matrix227-resume13-positive':101,
 'matrix227-resume13-negative':101,
 'equality227-resume13-mask-owned-zero':101,
 'equality227-resume13-negative':101,
 'equality227-resume13-negative-frozen-masks':101,
 'd188227-resume13-negative':1}
for r in native:
 assert r['swaps']==0
 assert r['limits']=={'memory.high':str(6*2**30),'memory.max':str(8*2**30),'memory.swap.max':'0','pids.max':'64'}
 assert r['exit_status']==codes.get(r['label'],0),(r['label'],r['exit_status'])
 assert r['source_revision']
 for gate in ['reservation.json','barrier.json']:
  assert json.loads((O/'receipts'/r['label']/gate).read_text())['allowed']is True
cov=json.loads((O/'coverage.json').read_text());assert (cov['bound'],cov['reclassification_bound'],cov['own_1_proved_fully_composed'])==(39,39,0)
identity=json.loads((O/'identity-audit.json').read_text());assert len(identity['new_bound'])==3
for r in identity['new_bound']:assert r['bound']
assert runjoin['conclusion_text_byte_identical']and not runjoin['full_requested_skeleton_complete']
assert (O/'slice-std-binding-resume13.json').exists()
std=json.loads((O/'slice-std-binding-resume13.json').read_text());assert all(r['token_identical']for r in std['rows'])
summary.update(native_receipts_verified=30,native_passes=sum(r['exit_status']==0 for r in native),native_nonzero=sum(r['exit_status']!=0 for r in native),coverage=dict(conservative_reachable_candidates=79,bound=39,reclassification_bound=39,own_1_proved_fully_composed=0,identity_checked=43,exact_deployed_cone_certified=False),full_requested_skeleton_complete=False,first15='Exact-conclusion core compiled on ordinal 14; full required grouped skeleton not completed',no_unchanged_failed_source_resubmission=True,guard_sha256=hashlib.sha256(Path('tools/pv-b3p6-20261028/compile_resume13.py').read_bytes()).hexdigest(),d188='four new owned/emission families, 16 finite comparisons; global source binding still open',matrix='270 exact arithmetic prefix snapshots, 2430 entry comparisons; final deployed result also compared 10 times; finite instrumentation, not universal proof',source_to_machine_boundary='V370 / pending owner D381,D386 retained',side_channels='unchanged; no side-channel privacy closure asserted',extra_own_input_rejection='An overlapping submit was refused by charged-ID guard before scope launch; serialized thereafter with local file lock. No compiler started or extra charged attempt.')
(O/'verification-summary.json').write_text(json.dumps(summary,indent=2)+'\n')
print(json.dumps({k:summary[k]for k in ['charged_attempts','passed','rejected','audit_ids','audited_theorems','native_receipts_verified','refusals_uncharged','coverage','target_established']}))
