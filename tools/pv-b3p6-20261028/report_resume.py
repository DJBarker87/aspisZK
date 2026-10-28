"""Index retained receipts and verify the accepted focused closure without rebuilding."""
from pathlib import Path
import json,hashlib,re,subprocess,shutil
D=Path('evidence/pv-b3p6-20261028');R=D/'receipts-resume'
t=json.loads((R/'TALLY-resume.json').read_text());assert t['lean_attempts']==100 and t['kani_runs']==0
assert sorted(t['used_ids'])==list(range(36400,36500))
(D/'TALLY-resume.json').write_text(json.dumps(t,indent=2)+'\n')
receipts=[];raw=[]
for p in sorted(R.glob('lean-*/receipt/receipt.json')):
 r=json.loads(p.read_text());raw.append((p,r))
 assert hashlib.sha256((p.parent.parent/'source.lean').read_bytes()).hexdigest()==r['source_sha256']
 if r['exit_status']==0:assert 'sorryAx' not in str(r['print_axioms'])
 fields=['attempt','module','exit_status','wall_seconds','peak_rss_kib','cgroup_memory_peak_bytes','swaps','source_sha256','deps_fingerprint','lean_source_revision','source_revision','print_axioms']
 receipts.append(dict({k:r.get(k) for k in fields},receipt=str(p),proof_credit=r['exit_status']==0))
assert len(receipts)==100 and len({r['attempt'] for r in receipts})==100
(D/'receipt-index-resume.json').write_text(json.dumps(dict(receipts=receipts,failed_drafts_have_no_credit=True,revision_corrections='resume-revision-corrections.json',kani_runs=0),indent=2)+'\n')
res=json.loads((D/'project-resolution.json').read_text());objs={r['path']:r['sha256'] for r in json.loads((D/'resume-object-manifest.json').read_text())['files']};checked=[];bad=[]
for mod,a in res['modules'].items():
 candidates=[(p,r) for p,r in raw if r['module']==mod and r['exit_status']==0 and r['source_sha256']==a['sha256']]
 assert candidates,mod
 p,r=max(candidates,key=lambda z:z[1]['attempt'])
 for dep,obj in r['dependency_objects'].items():
  if dep in res['modules'] and objs.get(obj['path'])!=obj['sha256']:bad.append(dict(module=mod,dependency=dep,object=obj))
 checked.append(dict(module=mod,receipt=str(p),source_sha256=a['sha256'],blob=a['blob']))
assert not bad,bad
(D/'closure-hash-audit-resume.json').write_text(json.dumps(dict(root=res['roots'],checked=checked,dependency_mismatches=bad,external_authority='h4; fresh external-verification.json',note='Exact source and private dependency object coherence for final focused closure; not endpoint release replay'),indent=2)+'\n')
s=json.loads((D/'row-status.json').read_text())
s['counter_snapshot']=dict(lean_attempts=100,kani_runs=0,resume_range=[36400,36499]);s['stop_reason']='Fresh Lean budget exhausted; no checked ledger-row or endpoint counterexample'
s['final_audits']=dict(axioms='36497 PASS',combined='36498 PASS',focused_closure='36499 PASS',scope='V229 selected callback/source/value closure and explicitly conditional V243 packet; no endpoint closure',axioms_allowed=['propext','Classical.choice','Quot.sound'])
for row in s['rows']:
 if row['id']=='V243':
  row['checked_theorems']+=['PV_B3P_'+n for n in ['FrontierValue226.complete_result','LateValue226.recipient/change/frontier/next_root/next_frontier','LayoutRegions226 (all thirteen region values)','ScalarValue226.asset/amount/index','VecValue226.push_value/u8_clone/u8_extend/extend_failure','AppendFields226.native_fields_complete','ArrayEight226.values','Chunk8Projection226.success_cell','SerializerBridge226.installed_value_of_cells (conditional only)']]
  row['native_finite_validation']='receipts-resume/native226-structural-resume/receipt/receipt.json; 2884 same-input complete-Result comparisons; finite validation only'
  row['last_checked_install']='receipts-resume/lean-36495/receipt/receipt.json'
  row['next_deliverable']='Prove 64-byte/23-chunk success projections and flatten cell values, close named cells premise, compose actual Vec/error paths and finish owned-copy to extracted-reference structural binding'
 if row['id'] in ['V228','V241','V245','V244']:
  row['next_deliverable']='Owned safe reference outside shipped crates, complete Result/value and original-carrier laws, script-checked structural native binding plus same-input finite validation; no Kani in this run'
for row in s['rows']:
 row['checked_theorems']=list(dict.fromkeys(row['checked_theorems']))
(D/'row-status.json').write_text(json.dumps(s,indent=2)+'\n')
b=json.loads((D/'owned226-binding.json').read_text());b.update(native_finite_validation='receipts-resume/native226-structural-resume/receipt/receipt.json; 2884 complete-Result same-input comparisons; finite validation',owned_to_extracted_reference='OPEN: 64-byte and 23-chunk projections/flatten cell composition plus actual native Vec/error composition. Checked region/layout/index/Vec helper laws do not discharge whole binding.',native_link_credit=False,row_closed=False);(D/'owned226-binding.json').write_text(json.dumps(b,indent=2)+'\n')
print(json.dumps(dict(total=len(receipts),passed=sum(r['exit_status']==0 for r in receipts),failed=sum(r['exit_status']!=0 for r in receipts),closure_modules=len(checked),dependency_mismatches=bad)))
