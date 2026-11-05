from pathlib import Path
import json,hashlib,copy,re,lzma
E=Path(__file__).resolve().parent
read=lambda name:json.loads((E/name).read_text())
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
standard={'propext','Classical.choice','Quot.sound'}
def check(bundle):
 a,c,d=bundle['audit'],bundle['closed'],bundle['delta']
 assert a['status']=='PARTIAL_TARGET_NOT_ESTABLISHED' and c['status']=='PARTIAL_MODEL_AND_LOCAL_NATIVE_ONLY'
 for n in ['source_scope_run_instantiated','equality_cut_source_closed','pending_runtime_trust_used']:assert a[n] is False,n
 for n in ['source_functions_closed','exclusive_guard_owners_complete','pool_consumer_rows_closed','held_boundaries_discharged']:assert a[n]==0,n
 assert c['source_scope_run_instantiated'] is False and c['source_functions_closed']==c['exclusive_guard_owners_complete']==c['held_boundaries_discharged']==0
 assert c['closed_pool_consumers']==d['closed']==[] and d['promoted_rows']==0
 assert a['trust_rows_added']==a['trust_rows_removed']==[]
 assert a['conditional_equality_native_passes']==c['conditional_equality_native_passes']==['NIZ_K009','NIZ_K023','NIZ_K025']
 assert a['quarantined_function_pointer_passes']==a['suspended_writable_static_passes']==[]
 assert a['caps']==dict(memory_high='6G',memory_max='8G',memory_swap_max=0,tasks_max=64,lean_M=7000,concurrent_scopes=1)
 assert a['budget']['kani_used']==37 and a['budget']['kani_limit']==120 and a['budget']['extraction_used']==a['budget']['extraction_limit']==0
 assert a['budget']['lean_slots_used']==len(list(E.glob('NIZ_L???/receipt.json')))<=60
 assert a['budget']['early_stop_below_80'] is True
 assert (a['budget']['kani_used']+a['budget']['lean_slots_used'])/(120+60)<0.8
 assert 'below 80 percent' in (E/'NIZ_REMAINING.md').read_text()
 assert len(read('NIZ_OPEN_SITES.json')['owners'])==13
 for r in read('NIZ_SOURCE_FREEZE.json')['modules']:
  assert sha(Path(r['path']))==r['sha256'] and Path(r['path']).read_bytes()==Path(r['snapshot']).read_bytes()
  p=E/r['attempt']/'receipt.json';assert sha(p)==r['receipt_sha256'] and json.loads(p.read_text())['exit_status']==0
 assert a['raw_standard_only'] is True and a['raw_summary_disagreements']==0 and a['raw_roots']==41
 raw=read('NIZ_audit/batch0/proof0.json');names=read('NIZ_AUDIT_ROOTS.json')['new_roots']
 assert len(names)==40 and len(raw['results'])==41 and {r['root'] for r in raw['results']}==set(names+['AspisR1.RPx_Deployed.deployed'])
 assert all(r['equal'] and set(r['walked_axioms'])<=standard for r in raw['results'])
 assert a['fixtures']['count']==8 and a['fixtures']['baseline_matches'] is True
 assert a['scan']['exit']==0 and a['scan']['modules']==13508 and a['scan']['dangling']==a['scan']['incompatible_owners']==a['scan']['import_mismatches']==0
 pins=read('NIZ_EXPORT.json');assert len(pins['exports'])==21 and pins['export_bytes']==sum(r['bytes'] for r in pins['exports'])
 closure=lzma.decompress((E/'NIZ_CLOSURE_PINS.json.xz').read_bytes());assert hashlib.sha256(closure).hexdigest()==(E/'NIZ_CLOSURE_PINS.json.sha256').read_text().strip()
 assert json.loads(closure)['modules']==13508
 n=read('NIZ_NATIVE_SUMMARY.json');assert n['counts']==dict(TIMEOUT=2,COMPILER_REJECTED=2,PASS=16,SEMANTIC_CONTROL_FAIL=17) and len(n['attempts'])==37
 for r in n['attempts']:
  a_id=r['attempt'];p=E/a_id/'receipt.json';assert sha(p)==r['receipt_sha256']
  cfg=read(a_id+'.json');ad=read(a_id+'-admission.json');graph=read(a_id+'-graph-check.json');lock=read(a_id+'-lock-check.json')
  assert ad['exit']==0 and ad['reservation']['allowed'] is True
  assert graph['graph_matches_frozen'] and graph['exact_LPm_graph'] and lock['unchanged'] and lock['before']==lock['after']
  assert cfg['env']['CARGO_NET_OFFLINE']=='true' and cfg['env']['CARGO_TARGET_DIR'].endswith('/NIZ_target') and cfg['env']['CARGO_PROFILE_DEV_OPT_LEVEL']=='3'
  assert cfg['copy_patch_sha256']=='bcdf749b78eb6143789500d98d64ec3d407b8a17a6d1290c70c822473e8e9a67'
  assert r['production_credit'] is False and read(a_id+'-rule16-check.json')['no_writable_static']
 s17=read('NIZ_K017-shape.json')['source'];s19=read('NIZ_K019-shape.json')['source'];assert s17==s19.replace('fn certificate_stability()','fn certificate()')
 assert not any(p.stat().st_size>20*1024*1024 for p in E.rglob('*') if p.is_file())
 return True
bundle={k:read(n) for k,n in [('audit','NIZ_AUDIT.json'),('closed','NIZ_CLOSED.json'),('delta','NIZ_LEDGER_DELTA.json')]}
check(bundle)
mutations=[('audit','source_scope_run_instantiated',True),('audit','source_functions_closed',1),('audit','exclusive_guard_owners_complete',1),('audit','pool_consumer_rows_closed',1),('audit','held_boundaries_discharged',1),('audit','equality_cut_source_closed',True),('audit','pending_runtime_trust_used',True),('audit','trust_rows_added',['RuntimeCpiReadonlyEntry7']),('audit','trust_rows_removed',['S2TrustedSdkBorrow']),('audit','conditional_equality_native_passes',[]),('audit','raw_standard_only',False),('audit','raw_roots',40),('closed','source_scope_run_instantiated',True),('closed','closed_pool_consumers',['fake']),('closed','held_boundaries_discharged',4),('closed','status','CLOSED'),('delta','closed',['fake']),('delta','promoted_rows',1)]
rejected=[]
for section,key,value in mutations:
 b=copy.deepcopy(bundle);b[section][key]=value
 try:check(b)
 except AssertionError:rejected.append(section+'.'+key)
 else:raise AssertionError('Misleading mutation survived: '+section+'.'+key)
(E/'NIZ_VALIDATION.json').write_text(json.dumps(dict(valid=True,rejected_misleading_mutations=rejected,source_functions_closed=0,warning='Checks evidence consistency; not an additional source/native proof.'),indent=2))
print('NIZ evidence validation PASS; '+str(len(rejected))+' misleading-closure mutations rejected; no source status promoted.')
