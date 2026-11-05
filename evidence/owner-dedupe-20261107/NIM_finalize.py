from pathlib import Path
import json,lzma,hashlib,collections,subprocess
E=Path(__file__).resolve().parent;H=lambda b:hashlib.sha256(b).hexdigest();J=lambda p:json.loads(p.read_text());put=lambda n,x:(E/n).write_text(json.dumps(x,indent=1)+'\n')
rs=[json.loads(l)for l in (E/'NIM_ATTEMPTS.jsonl').read_text().splitlines()];assert len(rs)==40
roots=J(E/'NIM_AUDIT_ROOTS.json')['roots'];results=[]
for i in range(7):
 x=J(E/'NIM_audit'/('batch'+str(i))/('proof'+str(i)+'.json'));results+=x['results']
reconciliation=J(E/'NIM_ROOT_RECONCILIATION.json');assert reconciliation['status']=='PASS_REQUIRED_RAW_ROOT_COVERAGE'
assert set(J(E/'NIM_AUDIT_ROOTS_CORRECTED.json')['roots'])<=set(r['root']for r in results)
assert all(set(r['walked_axioms'])<={'propext','Classical.choice','Quot.sound'}for r in results)
fixtures=J(E/'NIM_audit/fixtures/fixtures.json');assert fixtures['exit_status']==0 and len(fixtures['results'])==8
scan=J(E/'NIM_SCAN.json');assert scan['exit_status']==scan['dangling']==scan['incompatible_owners']==scan['import_mismatches']==0
binary=J(E/'NIM_L032/NIM_ProofDriver_BINARY_PIN.json')['sha256']
assert all(J(E/f'NIM_L{i:03}'/'NIM_ProofDriver_BINARY_PIN.json')['sha256']==binary for i in range(34,41))
resource=dict(slots=40,kinds=dict(collections.Counter(r['kind']for r in rs)),wall_seconds=sum(r['wall_seconds']for r in rs),peak_rss_kib=max(int(r['peak_rss_kib'])for r in rs),swaps=sum(int(r['swaps'])for r in rs),failures=[dict(attempt=r['attempt'],target=r['module'],exit=r['exit_status'])for r in rs if r['exit_status']],kani=0,extraction=0)
put('NIM_AUDIT.json',dict(status='PASS_REQUIRED_RAW_ROOTS_WITH_RETAINED_TOOL_FINDINGS',combined_import='NIM_COMBINED_IMPORT',full_composition_pass=True,roots=reconciliation['required_roots'],measured_raw_roots=len(results),executed_selected_strings=len(roots),axioms=sorted({a for r in results for a in r['walked_axioms']}),all_raw_summary_equal=False,root_reconciliation='NIM_ROOT_RECONCILIATION.json',retained_nonzero_audit_exits=['NIM_L039','NIM_L040'],raw_authoritative_ruling="(ab')(3)",fixtures=fixtures['results'],same_optimized_binary_sha256=binary,scanner='NIM_SCAN.json',resources=resource,new_theorems=0,security_target_established=False))
basepath=E.parent/'ledger11-20261107/NII_LEDGER.json.xz';base=json.loads(lzma.decompress(basepath.read_bytes()));by={r['row']:r for r in base['rows']};rows=[]
for pre,d in [('NHJ','slice-d-entry3-20261106'),('NHY','slice-d-entry4-20261106')]:
 assert J(E/('NIM_REPLAY_'+pre+'.json'))['exit_status']==0
 delta=J(E.parent/d/(pre+'_LEDGER_DELTA.json'));cert=J(E.parent/d/(pre+'_CLOSED.json'));claims={f['id']:f['model_theorem']for f in cert['functions']}
 for r in delta['rows']:
  if r['row']not in delta['new_closed_rows']:continue
  ns=[claims[c]for c in r['selected_claims']if c in claims];assert ns and all(n in roots for n in ns)
  rows.append(dict(row=r['row'],function=r['function'],provider=pre,previous_status=by[r['row']]['composed_status'],status='CLOSED',model_theorems=ns,retargeted_combined='NIM_'+pre+'_COMBINED_IMPORT',original_validator=str(Path('evidence')/d/(pre+'_certify.py')),retained_boundary='Original root domains, PhysicalInterpretation, runtime and P6/D188 option-A trust unchanged; no extraction/native observer premise removed'))
assert len(rows)==28 and len({r['row']for r in rows})==28
counts=collections.Counter(r['composed_status']for r in base['rows']);after=counts.copy()
for r in rows:after[r['previous_status']]-=1;after['CLOSED']+=1
put('NIM_LEDGER_DELTA.json',dict(schema_version=1,status='PASS',basis=str(basepath),basis_uncompressed_sha256=H(lzma.decompress(basepath.read_bytes())),frozen_revision='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387',before=dict(counts),after=dict(after),restored_NHJ_rows=14,additional_NHY_rows=14,rows=rows,new_native_proofs=0,security_target_established=False,gate=['NIM_L027','NIM_L032','NIM_L033']+[f'NIM_L{i:03}'for i in range(34,41)],trust_change='NONE; existing P6/D188 semantic transport remains reclassification, never removal'))
put('NIM_RESOURCES.json',resource)
print(json.dumps(dict(audit_roots=reconciliation['required_roots'],measured_raw_roots=len(results),executed_selected_strings=len(roots),before=dict(counts),after=dict(after),resources=resource)))
