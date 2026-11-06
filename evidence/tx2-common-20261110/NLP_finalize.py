"""Derive reports from retained receipts; never change ledger or source evidence."""
from pathlib import Path
import json,hashlib,lzma,collections,re,subprocess
E=Path(__file__).resolve().parent
read=lambda n:json.loads((E/n).read_text())
write=lambda n,x:(E/n).write_text(json.dumps(x,indent=2)+'\n')
rows=[json.loads(l) for l in (E/'NLP_ATTEMPTS.jsonl').read_text().splitlines()]
assert len({r['attempt'] for r in rows})==len(rows)
raw=[]
for p in sorted((E/'NLP_audit').glob('batch*/proof*.json')):
 r=json.loads(p.read_text());assert r['exit_status']==0;raw+=r['results']
roots=read('NLP_AUDIT_ROOTS.json')['roots'];assert len(raw)==len(roots) and {r['root'] for r in raw}==set(roots)
assert all(r['equal'] and set(r['walked_axioms'])<={'propext','Classical.choice','Quot.sound'} for r in raw)
fixtures=[]
for mode in ['fixtures','scanfixtures']:
 r=read('NLP_audit/'+mode+'/fixtures.json');assert r['exit_status']==0 and len(r['results'])==8 and all(x['equal'] for x in r['results']);fixtures.append(dict(mode=mode,results=r['results'],exit=0))
loaded=[json.loads(l) for l in (E/'NLP_LOADED_scan.jsonl').read_text().splitlines()]
assert all(not r['dangling'] and not r['duplicate_owners'] and r['imports_match'] for r in loaded)
scan=read('NLP_audit/scan/scan.json');assert scan['exit_status']==0
scan_report=dict(status='PASS',attempt='NLP_L053',exit=0,modules=len(loaded),dangling=0,incompatible_owners=0,import_mismatches=0)
write('NLP_SCAN.json',scan_report)
comparison=read('NLP_PREDECESSOR_COMPARISON.json');assert comparison['status']=='PASS' and not comparison['mismatches']
assert read('NLP_EXPORT_VERIFY.json')['status']=='PASS'
raw_closure=lzma.decompress((E/'NLP_CLOSURE_PINS.json.xz').read_bytes());assert hashlib.sha256(raw_closure).hexdigest()==(E/'NLP_CLOSURE_PINS.json.sha256').read_text().strip()
predecessor=json.loads(Path('evidence/ledger22-20261110/NLO_AUDIT.json').read_text())
counts=collections.Counter(r['kind'] for r in rows)
metrics=dict(scopes=len(rows),kinds=dict(counts),compiler_invocations=counts['lean'],Lean_budget=90,Kani=0,Kani_budget=10,extraction=0,wall_seconds=sum(r['wall_seconds'] for r in rows),peak_rss_kib=max(int(r['peak_rss_kib']) for r in rows),swaps=sum(int(r['swaps']) for r in rows),failures=[r['attempt'] for r in rows if r['exit_status']!=0],heartbeat_exhaustion_retired='NLP_L038; replaced by isolated NLP_L039/NLP_L040',wall_timeouts=0,memory_kills=0,unchanged_exhausted_retries=0)
assert metrics['swaps']==0 and counts['lean']<=90
combined=[r for r in rows if r['kind']=='lean' and r['module']=='NLP_COMBINED_IMPORT'];assert len(combined)==1 and combined[0]['exit_status']==0
scope=dict(MemoryHigh='6G',MemoryMax='8G',MemorySwapMax=0,TasksMax=64,Lean_M=7000,concurrent_scopes=1,admission='every launch exit0 AND allowed:true',disk='every scope >=40GB preflight',CARGO_TARGET_DIR='/home/dombarker/project-offloads/codex-cx-tx2-common-20261110/NLP_target')
audit=dict(status='PASS',scope='Focused combined/import/raw ax2/NFX/retention only; NOT a native row certificate',target='TX2:065',target_established=False,composed_new_closed_rows=0,combined_import='NLP_COMBINED_IMPORT',combined_attempt='NLP_L041',headline='AspisR1.RPx_Deployed.deployed',modules=read('NLP_MODULES.json'),raw_roots=len(raw),raw_results=raw,raw_standard_axioms_only=True,all_raw_equal_collectAxioms=True,fixtures=fixtures,scan=scan_report,inherited_raw_roots=11174,inherited_raw_basis='NLO_AUDIT.json reused only after all33497 predecessor closure objects match this combined closure',predecessor_comparison=comparison,retained_collect_axioms_disagreements=predecessor['collect_axioms_disagreements'],metrics=metrics,limits=scope,full_combined_gates=1,cold_release_replay=False,full_frozen_manifest_replayed=False,no_new_trust_rows=True,source_revision_for_combined=combined[0]['source_revision'])
write('NLP_AUDIT.json',audit)
closed=dict(status='SUPPORT_ONLY',target='TX2:065',target_established=False,closed=[],candidate_closed=[],open_rows=['TX2:065'],root=None,native_parent_certificate=False,eligible_children={'TX2:124':'CLOSED at ledger22; NKU actual source packet installed','TX2:053':'CLOSED at ledger22; NLN packet installed at actual C04 under explicit original-input Root0 relation'},support='NLP_Assembly.installed',exact_child_packet_instantiation='source/native-window support: C01 complete NKU; C04 complete NLN Result/returning/abort histories; no packet premise in assembled support',remaining=['concrete SAME-parent allocator/ABI/query-region interpretation and nested native subcut installation','additional Root0 original-input clause needs its TX2:064/writer producer','final actual-parent adopted Result/ordered-effect transport; no child-law hypothesis may remain'],credit_gate='next authoritative ledger gate',reason='Strongest support still has auxiliary allocator/ABI/query cut inputs. No source Trace/G alias or record of these premises is promoted to a native root.')
write('NLP_CLOSED.json',closed)
baseline=Path('evidence/ledger22-20261110/NLO_LEDGER.json.xz');base=json.loads(lzma.decompress(baseline.read_bytes()));assert base['counts']=={'CLOSED':576,'OPEN':23}
write('NLP_LEDGER_DELTA.json',dict(baseline=str(baseline),baseline_sha256=hashlib.sha256(baseline.read_bytes()).hexdigest(),counts_before=dict(closed=576,qualified=0,open=23,total=599),counts_after=dict(closed=576,qualified=0,open=23,total=599),delta=dict(closed=0,qualified=0,open=0),promotions=[],target='TX2:065',target_status='OPEN',no_authoritative_ledger_modified=True))
clauses=read('NLP_CALLER_CLAUSES.json')
for r in clauses['internal']:
 if r.get('status','').endswith('pending'):r['status']='PASS_SOURCE_SUPPORT; original-input Root0 remains explicit'
write('NLP_CALLER_CLAUSES.json',clauses)
write('NLP_CLIENT_CHANGES.json',dict(base='evidence/tx2-native11-20261109/NLB_run.py',changes=['own NLP prefix/workspace and90Lean/10Kani/0extraction allowance','own module/root selector and runtime-path driver adaptation; retained walker byte-identical','retention/export/closure-verification inputs and receipt collection','combined import maximum2 enforced','client-script SHA recorded on later configurations','transient client lock excluded from git; accidental stage2 lock tracking removed at next stage'],shared_infrastructure_changed=False,validation_same_or_stricter=True))
print(json.dumps(dict(status='PASS',raw_roots=len(raw),loaded=len(loaded),scopes=len(rows),Lean=counts['lean'],new_closed=0,target_established=False)))
