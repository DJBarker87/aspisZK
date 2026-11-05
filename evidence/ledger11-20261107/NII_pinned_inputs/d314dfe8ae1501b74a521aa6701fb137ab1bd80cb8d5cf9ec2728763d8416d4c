"""Add-only admission checks over the unchanged NFK validator.
Missing shape-fidelity controls deny all proposed native contract promotions.
"""
from pathlib import Path
import json,lzma,hashlib,re,sys,types,copy,collections
sys.dont_write_bytecode=True
E=Path(__file__).resolve().parent;R=E.parents[1]
J=lambda n:json.loads((E/n).read_text())
sha=lambda b:hashlib.sha256(b).hexdigest()
STANDARD={'propext','Classical.choice','Quot.sound'}
LOCK='5782e6a32026fdd95d252d0db7ea20b16716e6deb4f5a397e744886bb6ba22ef'
KMX='bcdf749b78eb6143789500d98d64ec3d407b8a17a6d1290c70c822473e8e9a67'
LIMITS={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'}
def put(n,x): (E/n).write_text(json.dumps(x,indent=1)+'\n')
def log(n):
 p=E/n
 return p.read_text() if p.exists() else lzma.decompress(p.with_name(p.name+'.xz').read_bytes()).decode()
def receipt(a):
 r=J(a+'/receipt.json');ad=J(a+'-admission.json')
 assert ad['exit']==0 and ad['reservation']['allowed'] is True
 assert r['limits']==LIMITS and int(r['swaps'])==0
 assert int(r['peak_rss_kib'])<8*1024*1024
 assert r['source_revision'] and 'wall_seconds' in r and 'print_axioms' in r
 return r

def native(k,status):
 a=f'NGL_K{k:03}';r=receipt(a);assert r['exit_status']==status
 assert J(a+'-graph-check.json')['graph_matches_frozen']
 l=J(a+'-lock-check.json');assert l['unchanged'] and l['before']==l['after']==LOCK
 assert not J(a+'-source-check.json')['errors']
 assert r['env']['CARGO_NET_OFFLINE']=='true' and r['env']['CARGO_PROFILE_DEV_OPT_LEVEL']=='3'
 assert '--locked' not in r['native_command']
 assert 'pool-adapter,private-leaf-salts' in r['native_command']
 return r,log(a+'/stdout.log')

def pair(p,n):
 a,x=native(p,0);b,y=native(n,1)
 assert a['module']==b['module'] and 'VERIFICATION:- SUCCESSFUL' in x
 assert 'VERIFICATION:- FAILED' in y and 'Failed Checks: |r|' in y
 assert re.search(r'\*\* 1 of \d+ failed',y)
 return a,b

def copy_pair(p,n,subject):
 a,x=native(p,0);b,y=native(n,1)
 assert 'VERIFICATION:- SUCCESSFUL' in x and 'VERIFICATION:- FAILED' in y
 assert re.search(r'\*\* 1 of \d+ failed',y)
 assert a['env']['RUSTFLAGS']==b['env']['RUSTFLAGS']==subject['env']['RUSTFLAGS']
 assert J('NGL_SOURCE_PINS.json')
 return {'positive':f'NGL_K{p:03}','negative':f'NGL_K{n:03}','patch_sha256':KMX}

def fidelity():
 return [
 {'function':'programs/r1-cost-probe/src/r1_pool_adapter.rs::readonly_meta_ok','rows':['TX2:223'],'interface':'(&Pubkey,&Pubkey,bool,bool,bool) -> Result<(),ProgramError>','inverted_ensures':'NGL_K038','missing':['real-body unimplied-caller assertion PASS','stub_verified unimplied-caller assertion FAIL','modifies-violation FAIL'],'status':'OPEN'},
 {'function':'programs/r1-cost-probe/src/r1_pool_adapter_owned.rs::require_readonly_account','rows':['TX2:236'],'interface':'(&OwnedAccount,&Pubkey) -> Result<(),ProgramError>','inverted_ensures':'NGL_K107','missing':['real-body unimplied-caller assertion PASS','stub_verified unimplied-caller assertion FAIL','modifies-violation FAIL'],'status':'OPEN'},
 {'function':'programs/r1-cost-probe/src/r1_pool_adapter_owned.rs::OwnedAccount::data','rows':['TX1:335','TX2:229'],'interface':"(&OwnedAccount) -> Result<&[u8],ProgramError>",'inverted_ensures':['NGL_K065','NGL_K071','NGL_K077']+[f'NGL_K{k:03}' for k in range(91,106,2)],'missing':['real-body unimplied-caller assertion PASS','stub_verified unimplied-caller assertion FAIL','modifies-violation FAIL'],'status':'OPEN'}]

def native_review():
 rows=[]
 for k in range(1,121):
  r=receipt(f'NGL_K{k:03}');native(k,r['exit_status']);rows.append(r)
 for p,n in [(37,38),(106,107),(64,65),(70,71),(76,77)]+[(k,k+1) for k in range(90,106,2)]:pair(p,n)
 copies=[]
 for cp,cn,subject in [(80,81,37),(80,81,106),(82,83,64),(80,81,70),(84,85,76),(63,67,90),(87,88,92),(108,109,94),(110,111,96),(112,113,98),(114,115,100),(116,117,102),(118,119,104)]:
  copies.append(copy_pair(cp,cn,receipt(f'NGL_K{subject:03}')))
 for k in [37,38,106,107,64,65,70,71,76,77]+list(range(90,106)):
  assert J(f'NGL_K{k:03}-erasure-check.json')['passed']
 x={'status':'PASS_EVIDENCE_CHECKS_NOT_ADMISSION','runs':120,'exits':dict(collections.Counter(str(x['exit_status']) for x in rows)),
    'graph_lock_source_offline_deployed_features_checked_every_run':True,'copy_controls':copies,'missing_shape_fidelity':fidelity(),
    'no_stub_verified_in_credited_callers':True,'new_admitted_rows':0,'ruling':'t; do not infer non-Bool interface fidelity from a matching inverted contract alone'}
 put('NGL_NATIVE_REVIEW.json',x);return x

def model_review():
 summary=J('NGL_final_audit/SUMMARY.json');assert summary['status']=='PASS'
 fixture=J('NGL_final_audit/fixtures.json');n=NFK();n.fixtures(fixture['results'])
 pin=J('NGL_final_audit/BINARY_PIN.json')['sha256'];audited={}
 groups=J('NGL_AUDIT_ROOTS.json')['groups']
 for i in range(len(groups)):
  directory='NGL_final_audit' if i<7 else 'NGL_delta_audit'
  d=J(f'{directory}/proof{i}.json');assert d['exit_status']==0 and int(d['swaps'])==0
  assert d['same_optimized_binary_sha256']==fixture['same_optimized_binary_sha256']==pin
  for r in d['results']:
   assert r['equal'] and set(r['walked_axioms'])==set(r['collect_axioms'])<=STANDARD
   name=f"NEP_proof{i}_{r['root']}_REACHABLE.txt";raw=lzma.decompress((E/(name+'.xz')).read_bytes());assert sha(raw)==(E/(name+'.sha256')).read_text().split()[0]
   audited[r['root']]={**r,'attempt':'NGL_L060' if i<7 else 'NGL_L068','raw_graph':name+'.xz','raw_graph_sha256':sha(raw),'group_receipt':f'{directory}/proof{i}.json'}
 assert set(audited)==set(J('NGL_AUDIT_ROOTS.json')['roots']) and len(audited)==56
 rows=[json.loads(l) for l in (E/'NGL_LOADED_scan.jsonl').read_text().splitlines()]
 assert receipt('NGL_L069')['exit_status']==0
 assert all(r['imports_match'] and not r['dangling'] and not r['duplicate_owners'] for r in rows)
 assert sha((E/'NGL_WALKER_SOURCE.lean.txt').read_bytes())==J('NGL_VALIDATOR_INPUT_PINS.json')['walker']['sha256']
 expected=J('NGL_VALIDATOR_INPUT_PINS.json')
 # Every delivered top theorem module is compiled from the exact final source.
 modules={r.rsplit('.',1)[0] for r in audited if r.startswith('NGL_')};compiles=[]
 for m in sorted(modules):
  s=sha((E/(m+'.lean')).read_bytes());matches=[]
  for p in E.glob('NGL_L???/receipt.json'):
   d=json.loads(p.read_text())
   if d['kind']=='lean' and d['module']==m and d['exit_status']==0 and s in d['source_hashes'].values():matches.append(d['attempt'])
  assert matches,m;compiles.append({'module':m,'source_sha256':s,'focused_successes':matches})
 out={'status':'PASS_AX2_AND_NFX; NO_NATIVE_PROMOTIONS','combined_import':'NGL_L067','headline':'AspisR1.RPx_Deployed.deployed','raw_roots':audited,'root_count':56,
      'standard_axioms_only':True,'same_optimized_binary_fixtures':fixture,'binary_sha256':pin,
      'source_coherence':{'attempt':'NGL_L069','modules':len(rows),'dangling':0,'conflicting_owners':0,'import_mismatches':0,'first_scan':'NGL_L061 (six missing expectations; retained; source-verified additions only)'},
      'focused_sources':compiles,'unchanged_NFK_validator_sha256':expected['unchanged_NFK_validator']['sha256'],
      'admission_blocker':'C3-BIN ruling (t) non-Bool interface fidelity; NGL_NATIVE_REVIEW.json',
      'trust_reclassification':'P6/D188 NativeContractSemanticTransport option A retained; not removal; no new runtime trust adopted'}
 put('NGL_AUDIT.json',out);return {'roots':56,'modules':len(rows),'axioms':'standard only'}

def NFK():
 raw=(E/'NGL_NFK_validate.py.txt').read_bytes();assert sha(raw)==J('NGL_VALIDATOR_INPUT_PINS.json')['unchanged_NFK_validator']['sha256']
 m=types.ModuleType('NGL_pinned_NFK');m.__file__=str(E/'NGL_NFK_validate.py.txt');exec(compile(raw,m.__file__,'exec'),m.__dict__);return m

def source_review():
 m=J('NGL_INPUTS.json');objects=m['objects']
 for h,r in objects.items():
  archive=(E/r['path']).read_bytes();assert sha(archive)==r['archive_sha256'];b=lzma.decompress(archive);assert sha(b)==h and len(b)==r['bytes']
 frozen=J('NGL_FROZEN_SOURCE_PINS.json')
 for path,h in m['frozen_source_files'].items():assert frozen[path]==h
 base=json.loads(lzma.decompress((E/'NGL_BASELINE_LEDGER.json.xz').read_bytes()));by={r['row']:r for r in base['rows']}
 for rid,ks in [('TX2:223',[37,38]),('TX2:236',[106,107]),('TX1:335',[64,65,70,71,76,77]+list(range(90,106)))]:
  row=by[rid];path=row['function'].split('::')[0];raw=lzma.decompress((E/objects[m['frozen_source_files'][path]]['path']).read_bytes());a,b=row['frozen_body_byte_range'];body=raw[a:b];assert sha(body)==row['frozen_body_sha256']
  for k in ks:
   h=m['attempts'][f'NGL_K{k:03}']['NGL_src/'+path];assert body in lzma.decompress((E/objects[h]['path']).read_bytes())
 assert not J('NGL_LIBRARY_BASE_COMPARISON.json')['selected_library_differences']
 assert J('NGL_RAW_TEMPLATES.json') and all(not x['admitted'] for x in J('NGL_RAW_TEMPLATES.json'))
 put('NGL_SOURCE_REVIEW.json',{'status':'PASS','unique_input_objects':len(objects),'attempt_input_sets':len(m['attempts']),'candidate_frozen_bodies_match':True,'library_vs_NGJ_base_differences':0,'shipped_file_changes':False,'ELF_rebuild_trigger':False,'unadmitted_templates_preserved':True})
 return {'input_objects':len(objects),'source_status':'PASS'}

def ledger_review():
 n=NFK();raw=lzma.decompress((E/'NGL_BASELINE_LEDGER.json.xz').read_bytes());assert sha(raw)==J('NGL_VALIDATOR_INPUT_PINS.json')['baseline']['uncompressed_sha256'];base=json.loads(raw);assert len(base['rows'])==599
 n.BASE_CREDITS=base['NEZ_credits']
 # There is no admissible candidate. Preserve the authoritative baseline exactly;
 # do not invent missing obligations for the newly inventoried OPEN error rows.
 incomplete=[r['row'] for r in base['rows'] if 'caller_domain_obligations' not in r]
 assert all(r['composed_status']=='OPEN' for r in base['rows'] if r['row'] in incomplete)
 assert all(x['missing'] and x['status']=='OPEN' for x in fidelity())
 out=copy.deepcopy(base);by={r['row']:r for r in out['rows']}
 assert out==base

 assert all(by[r['row']]['composed_status']==r['composed_status'] and by[r['row']]['selected_claims']==r['selected_claims'] for r in base['rows'])
 # Added admission gate is fail-closed even if a proposed packet calls itself closed.
 tests=[]
 for item in fidelity():
  assert item['missing'] and item['status']=='OPEN';tests.append({'function':item['function'],'denied':'missing shape-specific fidelity controls','inverted_ensures_available':item['inverted_ensures']})
 assert len(tests)==3
 b=next(r for r in base['rows'] if r['row']=='TX2:223');fake=copy.deepcopy(b);fake['frozen_body_sha256']='0'*64;assert 'candidate frozen identity mismatch' in n.row_checks(fake,b,{'id':'not a certificate'});tests.append({'mutation':'wrong frozen body','denied':True})
 try:n.certificate_checks(type('Support',(),{'support':lambda self,c:None})(),{'id':'bad','inner_hypotheses_remaining':['missing fidelity']})
 except ValueError:tests.append({'mutation':'residual inner hypothesis','denied':True})
 else:raise AssertionError('unchanged NFK accepted residual hypothesis')
 tiny=copy.deepcopy(base);tiny['rows']=[copy.deepcopy(b)]
 assert n.admit(tiny,{}, {},{'NGL':[]})['rows'][0]['composed_status']=='OPEN'
 archive=(E/'NGL_BASELINE_LEDGER.json.xz').read_bytes();(E/'NGL_COMPOSED_LEDGER.json.xz').write_bytes(archive);(E/'NGL_COMPOSED_LEDGER.json.sha256').write_text(sha(lzma.decompress(archive))+'\n')
 put('NGL_CANDIDATES.json',{'status':'ADMISSION_DENIED','functions':fidelity(),'not_progress_under_NDT':True})
 put('NGL_CLOSED.json',{'schema_version':1,'frozen_revision':base['frozen_revision'],'new_composed_functions':0,'new_composed_rows':0,'functions':[],'driver_root_status':'OPEN'})
 counts=dict(collections.Counter(r['composed_status'] for r in out['rows']))
 put('NGL_LEDGER_DELTA.json',{'baseline':'evidence/ledger8-20261105/NGJ_LEDGER.json.xz','new_closed_rows':[],'rows':[],'no_other_status_change':True,'validator_checks_added_only':True,'unchanged_NFK_validator_sha256':J('NGL_VALIDATOR_INPUT_PINS.json')['unchanged_NFK_validator']['sha256'],'checks_added':['per-run frozen graph/lock/offline/features/source','same-profile exact KMX controls','exact focused source hashes','56-root raw ax2 and same-binary fixtures','NFX source coherence','non-Bool contract-interface fidelity (missing: DENY)'],'mutation_tests':tests,'whole_ledger_counts_after':{'total':599,**counts},'trust_reclassification':'P6/D188 option A retained; no trust removed or added','spine_closed':0,'spine_total':13,'baseline_preserved_byte_exactly':True,'legacy_schema_incomplete_open_rows':incomplete,'admission_path':'all proposed candidates denied before NFK admission; no defaults added to incomplete rows; unchanged NFK denial checks and schema-complete OPEN no-promotion test executed','failed_bookkeeping_attempt':'NGL_L070 (retained); repaired locally without rerunning any proof'})
 return {'new_closed_rows':0,'mutation_denials':len(tests),'ledger_counts':counts}

def final_review():
 required=['NGL_SPINE.md','NGL_BRIDGES.md','NGL_DOMAINS.md','NGL_CLOSED.json','NGL_EDGES.json','NGL_LEDGER_DELTA.json','NGL_AUDIT.json','NGL_COMBINED_IMPORT.lean','NGL_HANDOFF.md','NGL_REMAINING.md','NGL_ATTEMPTS.jsonl']
 assert all((E/n).is_file() for n in required)
 assert J('NGL_CLOSED.json')['new_composed_rows']==0 and not J('NGL_LEDGER_DELTA.json')['new_closed_rows']
 assert J('NGL_AUDIT.json')['root_count']==56 and J('NGL_SOURCE_REVIEW.json')['status']=='PASS'
 spine=(E/'NGL_SPINE.md').read_text();assert len(re.findall(r'^\| TX[12]:\d+ .*\| OPEN \|',spine,re.M))==13
 oversized=[str(p.relative_to(E)) for p in E.rglob('*') if p.is_file() and p.stat().st_size>20*1024*1024];assert not oversized,oversized
 assert not list(E.rglob('__pycache__'))
 return {'required_outputs':required,'spine':'13 OPEN / 0 CLOSED','target_established':False,'all_inputs_under_20MiB':True,'admission':'DENIED for all three native contract candidates; exact missing fidelity controls recorded'}
