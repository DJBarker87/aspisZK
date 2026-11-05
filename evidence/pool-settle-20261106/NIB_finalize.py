"""Build auditable summaries from retained receipts; promote no ledger row."""
from pathlib import Path
import json,hashlib,lzma,re
E=Path(__file__).resolve().parent
J=lambda name:json.loads((E/name).read_text())
roots=J('NIB_AUDIT_ROOTS.json')['roots'];results=[]
for mode in ['batch0','batch1']:results+=J('NIB_audit/'+mode+'/proof'+('0' if mode=='batch0' else '1')+'.json')['results']
fixtures=J('NIB_audit/fixtures/fixtures.json')['results']
assert [r['root'] for r in results]==roots
assert all(r['equal'] and set(r['walked_axioms'])<={'propext','Classical.choice','Quot.sound'} for r in results)
assert len(fixtures)==8 and all(r['equal'] for r in fixtures)
assert [r['walked_axioms'] for r in fixtures]==[['NEP_Planted.matchAx'],['NEP_Planted.privateAx'],['NEP_Planted.proofAx'],['NEP_Planted.auxAx'],[],[],[],[]]
rows=[json.loads(l) for l in (E/'NIB_LOADED_scan.jsonl').read_text().splitlines()]
scan=dict(status='PASS',attempt='NIB_L019',modules=len(rows),declarations=sum(r['declarations'] for r in rows),references=sum(r['edges'] for r in rows),dangling=sum(len(r['dangling']) for r in rows),incompatible_owners=sum(len(r['duplicate_owners']) for r in rows),import_mismatches=sum(not r['imports_match'] for r in rows))
assert scan['dangling']==scan['incompatible_owners']==scan['import_mismatches']==0
assert J('NIB_L019/receipt.json')['exit_status']==0
(E/'NIB_SCAN.json').write_text(json.dumps(scan,indent=1)+'\n')
binaries=[J('NIB_L'+n+'/NIB_ProofDriver_BINARY_PIN.json') for n in ['015','016','017']]
assert binaries[0]==binaries[1]==binaries[2]
audit=dict(status='PASS',method='ax2 byte-identical NEP walker; adapted root/import/output lists; same optimized binary for fixtures and roots',roots=results,root_count=len(results),standard_axioms_only=True,fixture_results=fixtures,all_batches_same_binary=True,proof_binary=binaries[0],walker=J('NIB_WALKER_IDENTITY.json'),scan=scan,combined_attempt='NIB_L013',combined_source_sha256=hashlib.sha256((E/'NIB_COMBINED_IMPORT.lean').read_bytes()).hexdigest(),scope=dict(MemoryHigh='6G',MemoryMax='8G',MemorySwapMax=0,TasksMax=64,lean_M=7000),reused='NGK/NFV canonical exports and pinned coherent SInt2 closure; not a cold release replay',failed_attempts_excluded=['NIB_L001','NIB_L008','NIB_L009','NIB_L018'])
(E/'NIB_AUDIT.json').write_text(json.dumps(audit,indent=1)+'\n')
delta=dict(plan_row='POOL.read_to_settlement',plan_theorem_status='OPEN',model_subtheorem_status='PROVED-conditional',theorem='NIB_ReadToSettlement.read_to_settlement',print_axioms=['propext','Classical.choice','Quot.sound'],rows=[],composed_rows_added=0,closed_by_this_job=0,before=dict(B='OPEN',D='OPEN',Pool_production_association='OPEN'),after=dict(B='OPEN',D='OPEN',Pool_production_association='OPEN'),pending_candidates=['NIB-P1','NIB-P2','NIB-P3','NIB-P4'],trust_added=[],trust_removed=[],RuntimeCpiReadonlyEntry7='PENDING; UNUSED')
(E/'NIB_LEDGER_DELTA.json').write_text(json.dumps(delta,indent=1)+'\n')
attempts=[json.loads(l) for l in (E/'NIB_ATTEMPTS.jsonl').read_text().splitlines()]
assert len(attempts)<=50
for a in attempts:
 ad=J(a['attempt']+'-admission.json');assert ad['exit']==0 and ad['reservation']['allowed'] is True
assert all((r['swaps']=='0' or r['swaps']==0) for r in attempts)
(E/'NIB_BUDGET.json').write_text(json.dumps(dict(Lean_scopes=len(attempts),Lean_limit=50,Kani=0,Kani_limit=0,extraction=0,extraction_limit=0,successful_scopes=sum(r['exit_status']==0 for r in attempts),failed_scopes=sum(r['exit_status']!=0 for r in attempts),whole_budget_review='NIB_REMAINING.md; all available Lean model obligations complete, remaining items5–8 need native producer/continuation packets'),indent=1)+'\n')
print(json.dumps(dict(audit='PASS',roots=len(results),scan=scan,scopes=len(attempts))))
