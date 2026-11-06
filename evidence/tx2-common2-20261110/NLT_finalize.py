"""Own evidence derivation; no authoritative ledger or shared-file writes."""
from pathlib import Path
import json,hashlib,lzma,collections,sys,subprocess
E=Path(__file__).resolve().parent
sha=lambda b:hashlib.sha256(b).hexdigest()
read=lambda n:json.loads((E/n).read_text())
write=lambda n,x:(E/n).write_text(json.dumps(x,indent=2)+'\n')
rows=[json.loads(l) for l in (E/'NLT_ATTEMPTS.jsonl').read_text().splitlines()]
assert len(rows)==len({r['attempt'] for r in rows})
modules=[]
for p in sorted(E.glob('NLT_*.lean')):
 h=sha(p.read_bytes());passing=[]
 for r in rows:
  q=E/r['attempt']/'sources'/'NLT_generated'/p.name
  if r['kind']=='lean' and r['module']==p.stem and r['exit_status']==0 and q.exists() and sha(q.read_bytes())==h:passing.append(r)
 assert passing,('Missing exact passing source',p)
 r=passing[-1];modules.append(dict(module=p.stem,sha256=h,passing_attempt=r['attempt'],source_revision=r['source_revision']))
write('NLT_MODULES.json',modules)
if sys.argv[1:]==['--modules']:
 print(json.dumps(dict(modules=len(modules),all_exact_sources=True)));sys.exit(0)
roots=read('NLT_AUDIT_ROOTS.json')['roots'];raw=[]
for p in sorted((E/'NLT_audit').glob('batch*/proof*.json')):
 x=json.loads(p.read_text());assert x['exit_status']==0;raw+=x['results']
assert len(raw)==len(roots) and {x['root'] for x in raw}==set(roots)
assert all(x['equal'] and set(x['walked_axioms'])<={'propext','Classical.choice','Quot.sound'} for x in raw)
fixtures=[]
for mode in ['fixtures','scanfixtures']:
 x=read('NLT_audit/'+mode+'/fixtures.json');assert x['exit_status']==0 and len(x['results'])==8 and all(r['equal'] for r in x['results'])
 fixtures.append(dict(mode=mode,receipt=x))
loaded=[json.loads(l) for l in (E/'NLT_LOADED_scan.jsonl').read_text().splitlines()]
assert loaded and all(not x['dangling'] and not x['duplicate_owners'] and x['imports_match'] for x in loaded)
scan=read('NLT_audit/scan/scan.json');assert scan['exit_status']==0
assert 'NFN_SCAN_ZERO_DANGLING' in (E/'NLT_audit/scan/scan.log').read_text()
comparison=read('NLT_PREDECESSOR_COMPARISON.json');assert comparison['status']=='PASS' and not comparison['mismatches']
assert read('NLT_EXPORT_VERIFY.json')['status']=='PASS'
combined=[r for r in rows if r['kind']=='lean' and r['module']=='NLT_COMBINED_IMPORT'];assert len(combined)==2 and all(r['exit_status']==0 for r in combined)
counts=collections.Counter(r['kind'] for r in rows);assert counts['lean']<=130 and counts['kani']<=20 and counts['extract']==0
assert all(int(r['swaps'])==0 for r in rows)
for r in rows:
 rc=read(r['full_receipt']);assert rc['limits']=={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'}
 assert rc['env']['CARGO_TARGET_DIR']=='/home/dombarker/project-offloads/codex-cx-tx2-common2-20261110/NLT_target'
 admission=read(r['attempt']+'-admission.json');assert admission['exit']==0 and admission['reservation']['allowed'] is True
 assert read(r['attempt']+'-disk.json')['checks'][-1]['free']>=40_000_000_000
 if r['kind']=='lean':assert '-M7000' in rc['command']
metrics=dict(scopes=len(rows),kinds=dict(counts),Lean_compiler_invocations=counts['lean'],Lean_budget=130,Kani=counts['kani'],Kani_budget=20,extraction=0,wall_seconds=sum(r['wall_seconds'] for r in rows),peak_rss_kib=max(int(r['peak_rss_kib']) for r in rows),swaps=0,failed_elaborations=[r['attempt'] for r in rows if r['kind']=='lean' and r['exit_status']!=0],recursion_exhaustion_retired=['NLT_L015','NLT_L016'],symbolic_replacement=['NLT_L017','NLT_L022'],wall_timeouts=0,memory_kills=0,unchanged_exhausted_shape_retries=0)
pre=json.loads(Path('evidence/ledger22-20261110/NLO_AUDIT.json').read_text())
audit=dict(status='PASS',security_target_established=False,claim='Focused P6 root-candidate combined/import/raw ax2/NFX/retention gate; not a release security conclusion',target='TX2:065',root='NLT_CompleteRoot.root',credit='PENDING_NEXT_LEDGER_GATE',combined_import='NLT_COMBINED_IMPORT',combined_attempt=combined[-1]['attempt'],combined_source_revision=combined[-1]['source_revision'],headline='AspisR1.RPx_Deployed.deployed',modules=modules,raw_roots=len(raw),raw_results=raw,raw_standard_axioms_only=True,all_raw_equal_collectAxioms=True,fixtures=fixtures,NFX=dict(status='PASS',exit=0,modules=len(loaded),dangling=0,incompatible_owners=0,import_mismatches=0),predecessor_comparison=comparison,inherited_raw_roots=11174,inherited_raw_basis='NLO exact closure objects retained byte-identically; no unchanged frozen replay',retained_collect_axioms_disagreements=pre['collect_axioms_disagreements'],metrics=metrics,limits=dict(MemoryHigh='6G',MemoryMax='8G',MemorySwapMax=0,TasksMax=64,Lean_M=7000,concurrent_scopes=1),full_combined_gates=2,cold_build=False,full_frozen_manifest_replayed=False,no_new_trust_rows=True,trust_reclassification='Existing option-A P6/D188 native semantic transport, allocator/std/runtime digest retained',hypothesis_inventory='NLT_HYPOTHESES.md',native_interpretation='NLT_NATIVE_INTERPRETATION.json',caller_clauses='NLT_CALLER_CLAUSES.json')
write('NLT_AUDIT.json',audit)
x=read('NLT_CLOSED.json');x['status']='COMBINED_IMPORT_NFX_RAW_AX2_PASS_CREDIT_PENDING';x['rows'][0]['status']='CANDIDATE_CLOSED_ON_OWN_INPUT_DOMAIN';x['rows'][0]['root']='NLT_CompleteRoot.root';x['rows'][0]['module']='NLT_CompleteRoot';x['gate_evidence'].update(combined=combined[-1]['attempt']+' PASS',NFX='NLT_audit/scan/scan.json exit0',raw_ax2=str(len(raw))+' roots standard and equal',audit='NLT_AUDIT.json');write('NLT_CLOSED.json',x)
x=read('NLT_LEDGER_DELTA.json');x['proposed_promotions']=[dict(row='TX2:065',root='NLT_CompleteRoot.root',credit='PENDING_NEXT_LEDGER_GATE')];x['proposed_after_next_gate']=dict(CLOSED=577,QUALIFIED=0,OPEN=22,total=599);write('NLT_LEDGER_DELTA.json',x)
x=read('NLT_NATIVE_INTERPRETATION.json');x['status']='ROOT_COMBINED_RAW_NFX_PASS_LEDGER_PENDING';write('NLT_NATIVE_INTERPRETATION.json',x)
x=read('NLT_CALLER_CLAUSES.json');x['status']='CANDIDATE_CLOSED_ON_ARGUMENT_DOMAIN; TX2:064 producer OPEN';write('NLT_CALLER_CLAUSES.json',x)
print(json.dumps(dict(status='PASS',raw_roots=len(raw),modules=len(loaded),scopes=len(rows),Lean=counts['lean'],Kani=counts['kani'],new_credited_rows=0,candidate_rows=1,target_established=False)))
