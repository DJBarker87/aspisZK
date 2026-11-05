from pathlib import Path
import json,hashlib,re,subprocess,collections,lzma
E=Path(__file__).resolve().parent;I=E.parent/'pool-borrow2-20261107'
read=lambda p:json.loads(p.read_text());sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
receipts=[read(p) for p in sorted(E.glob('NIZ_[KL]???/receipt.json'))]
native=[]
for p in sorted(E.glob('NIZ_K???/receipt.json')):
 d=read(p);a=p.parent.name;s=(p.parent/'stdout.log').read_text();tail=s[s.find('Checking harness'):] if 'Checking harness' in s else s
 shape=read(E/(a+'-shape.json'));cfg=read(E/(a+'.json'))
 assert read(E/(a+'-admission.json'))['exit']==0 and read(E/(a+'-admission.json'))['reservation']['allowed'] is True
 assert read(E/(a+'-graph-check.json'))['graph_matches_frozen'] and read(E/(a+'-graph-check.json'))['exact_LPm_graph']
 assert read(E/(a+'-lock-check.json'))['unchanged']
 assert read(E/(a+'-rule16-check.json'))['no_writable_static']
 assert cfg['env']['CARGO_NET_OFFLINE']=='true' and cfg['env']['CARGO_TARGET_DIR'].endswith('/NIZ_target')
 assert cfg['env']['CARGO_PROFILE_DEV_OPT_LEVEL']=='3' and cfg['copy_patch_sha256']=='bcdf749b78eb6143789500d98d64ec3d407b8a17a6d1290c70c822473e8e9a67'
 if 'CBMC timed out.' in tail:status='TIMEOUT'
 elif d['exit_status']==0 and 'VERIFICATION:- SUCCESSFUL' in tail:status='PASS'
 elif 'Failed Checks: assertion failed:' in tail and 'VERIFICATION:- FAILED' in tail and shape['expected_verdict']=='FAIL':status='SEMANTIC_CONTROL_FAIL'
 elif re.search(r'^error(?:\[|:)',s,re.M):status='COMPILER_REJECTED'
 else:raise AssertionError((a,'unclassified'))
 native.append(dict(attempt=a,status=status,member=shape.get('member'),kind=shape['kind'],receipt_sha256=sha(p),production_credit=False,conditional_equality_cut='NIZ_eq' in shape.get('source',''),frame_or_reply_failures=[l for l in tail.splitlines() if l.startswith('Failed Checks:')]))
counts=dict(collections.Counter(r['status'] for r in native));assert len(native)==37
(E/'NIZ_NATIVE_SUMMARY.json').write_text(json.dumps(dict(counts=counts,attempts=native,source_functions_closed=0),indent=2))
current={'NIZ_LAYOUT':1,'NIZ_Unique':5,'NIZ_CallbackLayout':6,'NIZ_Memcmp':10,'NIZ_KeyEquality':12,'NIZ_AliasWindow':13,'NIZ_Dominance':14,'NIZ_SiteBounds':15,'NIZ_Noop':16,'NIZ_Groups':18,'NIZ_Cuts':19,'NIZ_Invariant':20,'NIZ_COMBINED_IMPORT':21,'NIZ_Driver':22,'NIZ_ProofDriver':23}
source_pins=[]
for name,number in current.items():
 a=f'NIZ_L{number:03d}';p=E/(name+'.lean');snapshot=E/a/'sources/NIZ_generated'/(name+'.lean')
 assert read(E/a/'receipt.json')['exit_status']==0 and p.read_bytes()==snapshot.read_bytes(),name
 source_pins.append(dict(module=name,attempt=a,path=str(p),sha256=sha(p),snapshot=str(snapshot),receipt_sha256=sha(E/a/'receipt.json')))
(E/'NIZ_SOURCE_FREEZE.json').write_text(json.dumps(dict(modules=source_pins),indent=2))
raw=read(E/'NIZ_audit/batch0/proof0.json');fixtures=read(E/'NIZ_audit/fixtures/fixtures.json')
roots=read(E/'NIZ_AUDIT_ROOTS.json');expected=roots['new_roots']+['AspisR1.RPx_Deployed.deployed'];standard={'propext','Classical.choice','Quot.sound'}
assert {r['root'] for r in raw['results']}==set(expected) and len(raw['results'])==41
assert raw['exit_status']==0 and all(r['equal'] and set(r['walked_axioms'])<=standard for r in raw['results'])
old=read(I/'NIO_audit/fixtures/fixtures.json');fields=['root','collect_axioms','walked_axioms','equal']
assert [{k:r[k] for k in fields} for r in fixtures['results']]==[{k:r[k] for k in fields} for r in old['results']]
proofpins=[read(E/f'NIZ_L{n:03d}/NIZ_ProofDriver_BINARY_PIN.json') for n in [26,27,28]];assert proofpins[0]==proofpins[1]==proofpins[2]
scan=[json.loads(l) for l in (E/'NIZ_LOADED_scan.jsonl').read_text().splitlines()]
metrics=dict(modules=len(scan),declarations=sum(r['declarations'] for r in scan),references=sum(r['edges'] for r in scan),dangling=sum(len(r['dangling']) for r in scan),incompatible_owners=sum(len(r['duplicate_owners']) for r in scan),import_mismatches=sum(not r['imports_match'] for r in scan))
assert not(metrics['dangling'] or metrics['incompatible_owners'] or metrics['import_mismatches'])
assert read(E/'NIZ_L028/receipt.json')['exit_status']==0
walker=E/'NIZ_L025/sources/NIZ_native/NFA_WALKER.c';assert walker.read_bytes()==(I.parent/'pool-borrow-20261107/NIK_L016/sources/NIK_native/NFA_WALKER.c').read_bytes()
(E/'NIZ_NFA_WALKER_PIN.json').write_text(json.dumps(dict(path=str(walker),sha256=sha(walker),unchanged=True),indent=2))
closed=dict(status='PARTIAL_MODEL_AND_LOCAL_NATIVE_ONLY',source_functions_closed=0,exclusive_guard_owners_complete=0,source_scope_run_instantiated=False,closed_pool_consumers=[],held_boundaries_discharged=0,local_default_noop_packet=True,new_model_theorems=40,raw_roots=41,conditional_equality_native_passes=['NIZ_K009','NIZ_K023','NIZ_K025'])
(E/'NIZ_CLOSED.json').write_text(json.dumps(closed,indent=2))
ledger=E.parent/'native-ledger3-20261029/NDT_LEDGER.json'
delta=dict(scope='Pool-consumer rows only',basis_path=str(ledger),basis_sha256=sha(ledger),frozen_revision='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387',closed=[],promoted_rows=0,warning='No local model/native observation or conditional cut is a composed source consumer.')
(E/'NIZ_LEDGER_DELTA.json').write_text(json.dumps(delta,indent=2))
by_kind=dict(collections.Counter(r['kind'] for r in receipts));lean_used=sum(r['attempt'].startswith('NIZ_L') for r in receipts)
audit=dict(status='PARTIAL_TARGET_NOT_ESTABLISHED',source_revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),source_tree_dirty=True,headline='AspisR1.RPx_Deployed.deployed',frozen_revision=delta['frozen_revision'],new_model_theorems=40,raw_roots=41,raw_exit=read(E/'NIZ_L027/receipt.json')['exit_status'],raw_standard_only=True,raw_summary_disagreements=sum(not r['equal'] for r in raw['results']),scan=dict(attempt='NIZ_L028',exit=0,**metrics),fixtures=dict(attempt='NIZ_L026',count=8,baseline_matches=True,proof_driver_sha256=proofpins[0]['sha256'],walker_sha256=sha(walker)),budget=dict(kani_used=len(native),kani_limit=120,lean_slots_used=lean_used,lean_slot_limit=60,extraction_used=0,extraction_limit=0,by_kind=by_kind,early_stop_below_80=True,member_by_member_reasons='NIZ_REMAINING.md'),source_scope_run_instantiated=False,source_functions_closed=0,exclusive_guard_owners_complete=0,pool_consumer_rows_closed=0,held_boundaries_discharged=0,equality_cut_source_closed=False,conditional_equality_native_passes=closed['conditional_equality_native_passes'],pending_runtime_trust_used=False,trust_rows_added=[],trust_rows_removed=[],accepted_pool_entry_admission_used_in_model=True,native_contract_transport='Retained P6/D188 option A: reviewed transcription reclassification, never premise removal',quarantined_function_pointer_passes=[],suspended_writable_static_passes=[],caps=dict(memory_high='6G',memory_max='8G',memory_swap_max=0,tasks_max=64,lean_M=7000,concurrent_scopes=1),artifacts=dict(sources='NIZ_SOURCE_FREEZE.json',closure='NIZ_CLOSURE_PINS.json.xz',exports='NIZ_EXPORT.json',raw='NIZ_audit/batch0/proof0.json',remaining='NIZ_REMAINING.md'))
(E/'NIZ_AUDIT.json').write_text(json.dumps(audit,indent=2))
# Per-attempt path annotation does not rewrite historical launcher receipts.
(E/'NIZ_TARGET_DIR_RECEIPTS.json').write_text(json.dumps([dict(attempt=r['attempt'],cargo_target_dir='/home/dombarker/project-offloads/codex-cx-pool-borrow3-20261107/NIZ_target',used=r['kind']=='kani',note='Unused for Lean/inspection/link/audit; explicit env set in all native runs.') for r in receipts],indent=2))
print('NIZ final register: '+str(len(native))+' native, '+str(lean_used)+' Lean/auxiliary receipts; 41 standard raw roots, eight matching fixtures, '+str(len(scan))+'-module clean scan; zero Pool promotions.')
