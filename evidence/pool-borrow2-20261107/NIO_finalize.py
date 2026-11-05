"""Build honest final summaries from retained receipts; never runs proof tools."""
from pathlib import Path
import json,hashlib,collections,re,subprocess
E=Path(__file__).resolve().parent
read=lambda p:json.loads(p.read_text())
current={'NIO_Cpi':6,'NIO_Infos':7,'NIO_Nested':8,'NIO_Windows':9,'NIO_AbortScopes':10,'NIO_LoopModel':11,'NIO_Invariant':12,'NIO_COMBINED_IMPORT':13,'NIO_Driver':14,'NIO_ProofDriver':15}
receipts=[read(p) for p in sorted(E.glob('NIO_[KLE]???/receipt.json'))]
by_kind=collections.Counter(x['kind'] for x in receipts)
raw=read(E/'NIO_audit/batch0/proof0.json')['results'];fixtures=read(E/'NIO_audit/fixtures/fixtures.json')['results']
baseline=read(E.parent/'pool-borrow-20261107/NIK_audit/fixtures/fixtures.json')['results'];assert fixtures==baseline
scan=[json.loads(l) for l in (E/'NIO_LOADED_scan.jsonl').read_text().splitlines()]
metrics=dict(modules=len(scan),declarations=sum(r['declarations'] for r in scan),references=sum(r['edges'] for r in scan),dangling=sum(len(r['dangling']) for r in scan),incompatible_owners=sum(len(r['duplicate_owners']) for r in scan),import_mismatches=sum(not r['imports_match'] for r in scan))
proof_pin=read(E/'NIO_L018/NIO_ProofDriver_BINARY_PIN.json');assert proof_pin==read(E/'NIO_L019/NIO_ProofDriver_BINARY_PIN.json')
walker=read(E/'NIO_NFA_WALKER.c_PIN.json');baseline_walker=E.parent/'pool-borrow-20261107/NIK_L016/sources/NIK_native/NFA_WALKER.c';assert walker['sha256']==hashlib.sha256(baseline_walker.read_bytes()).hexdigest()
standard={'propext','Classical.choice','Quot.sound'};assert len(raw)==37 and all(set(r['walked_axioms'])<=standard for r in raw)
closed=dict(status='PARTIAL_NATIVE_INPUTS_ONLY',complete_source_functions=0,source_scope_run_instantiated=False,closed_pool_consumers=[],model_theorems=36,raw_roots=37,local_native_observations=read(E/'NIO_NATIVE_SUMMARY.json'),warning='No reference-only scope or locally restricted native observation is a complete original-source certificate.')
(E/'NIO_CLOSED.json').write_text(json.dumps(closed,indent=2)+'\n')
delta=dict(slice='Pool-consumer',base_inventory='evidence/native-ledger3-20261029/NDT_LEDGER.json',frozen_revision='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387',promote_to_closed=[],rows_changed=[],non_pool_rows_changed=[],reason='No complete original-source owner/domain/native/model composition; local facts retained as inputs only.')
(E/'NIO_LEDGER_DELTA.json').write_text(json.dumps(delta,indent=2)+'\n')
audit=dict(status='PARTIAL_NOT_DEPLOYED_INVARIANT',source_revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),source_tree_dirty=True,frozen_revision=delta['frozen_revision'],headline='AspisR1.RPx_Deployed.deployed',current_module_attempts={m:f'NIO_L{n:03d}' for m,n in current.items()},new_model_theorems=36,raw_roots=37,raw_exit=read(E/'NIO_L019/receipt.json')['exit_status'],raw_standard_only=True,raw_summary_disagreements=sum(not r['equal'] for r in raw),scan=dict(attempt='NIO_L020',exit=read(E/'NIO_L020/receipt.json')['exit_status'],method='NFX owner/import/reference scan with unchanged ax2 walker',**metrics),fixtures=dict(attempt='NIO_L018',count=len(fixtures),baseline_matches=True,proof_driver_sha256=proof_pin['sha256'],walker_sha256=walker['sha256']),budget=dict(kani_used=by_kind['kani'],kani_limit=120,lean_slots_used=sum(x['attempt'].startswith('NIO_L') for x in receipts),lean_slot_limit=60,extraction_used=by_kind['extract'],extraction_limit=1,by_kind=dict(by_kind)),pending_runtime_trust_used=False,trust_rows_added=[],trust_rows_removed=[],source_scope_run_instantiated=False,source_functions_closed=0,pool_consumer_rows_closed=0,quarantined_function_pointer_passes=[],suspended_writable_static_passes=[],caps=dict(memory_high='6G',memory_max='8G',memory_swap_max=0,tasks_max=64,lean_M=7000,scopes_per_job=1),artifacts=dict(source_freeze='NIO_SOURCE_FREEZE.json',closure='NIO_CLOSURE_PINS.json.xz',exports='NIO_EXPORT.json',raw='NIO_audit/batch0/proof0.json',remaining='NIO_REMAINING.md'))
(E/'NIO_AUDIT.json').write_text(json.dumps(audit,indent=2)+'\n')
summary=dict(scopes=len(receipts),by_kind=dict(by_kind),exit_counts=dict(collections.Counter(str(x['exit_status']) for x in receipts)),wall_seconds=sum(x['wall_seconds'] for x in receipts),resource_receipts_complete=all(all(x.get(k) is not None for k in ['wall_seconds','peak_rss_kib','swaps','source_revision','source_hashes','limits']) for x in receipts),source_and_dep_pins='Per-scope receipt/config plus exact source snapshots; actual resolved closure retained by SHA.')
(E/'NIO_SUMMARY.json').write_text(json.dumps(summary,indent=2)+'\n')
print('Final summary generated: '+str(len(receipts))+' scoped receipts, 37 raw roots, zero Pool promotions')
