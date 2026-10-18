from pathlib import Path
import importlib.util,json,copy,hashlib,shutil
S=Path('/home/dombarker/project-offloads/aspis-r1-worker-c-selected-current-20261017');A=Path('/home/dombarker/project-offloads/aspis-r1-worker-a-rounds-proof-20261017');W=Path('/home/dombarker/project-offloads/aspis-r1-worker-c-source-read-proof-20261018')
spec=importlib.util.spec_from_file_location('r',S/'runner.py');r=importlib.util.module_from_spec(spec);spec.loader.exec_module(r)
D=json.loads((S/'external-inputs.json').read_text());a=json.loads((A/'sampler-current-object-pins.json').read_text());m=r.staged(S);assert len(m['modules'])==215
assert D['runtime_files']==a['runtime_files'] and D['olean_header_seal']==a['olean_header_seal']
identity=lambda v:(v['source_sha256'],{k:z['sha256'] for k,z in v['objects'].items()},v['imports'])
common=[]
for n,v in a['modules'].items():
 if n in D['modules']:
  assert identity(D['modules'][n])==identity(v),('conflicting current snapshots',n)
  common.append(n)
 else:
  item=copy.deepcopy(v)
  implicit_imports=r.imports(v['source'],True);assert v['imports'] in [r.imports(v['source']),implicit_imports],('actual source imports differ',n)
  item['imports']=implicit_imports
  source_root=str(Path(v['source']).parents[len(n.split('.'))-1]);object_roots={str(Path(ob['path']).parents[len(n.split('.'))-1]) for ob in v['objects'].values()};assert len(object_roots)==1,(n,object_roots)
  root_name='current_a_import_'+str(len(D['roots']))
  item['root']=root_name;D['roots'].append({'name':root_name,'source':source_root,'objects':object_roots.pop()})
  D['modules'][n]=item
roots={v['name']:v for v in D['roots']}
for v in a['roots']:
 if v['name'] in roots:assert roots[v['name']]==v,('root names differ',v['name'])
 else:D['roots'].append(v);roots[v['name']]=v
for p,h in a['provenance_files'].items():
 if p in D['provenance_files']:assert D['provenance_files'][p]==h
 D['provenance_files'][p]=h
D['provenance_files'][str(A/'sampler-current-object-pins.json')]=r.sha(A/'sampler-current-object-pins.json')
D['roots'].append({'name':'selected_current_215','source':str(S/'sources'),'objects':str(S/'objects')})
producing=[]
for n in m['topological_order']:
 rp=S/'successful-targets'/(n+'.json');rc=json.loads(rp.read_text());v=m['modules'][n];src=S/'sources'/v['stage_as'];ob=r.object_pins(S/'objects',n,D['olean_header_seal'])
 assert rc['exit_status']==0 and rc['axioms']['passed'] and rc['key']['source_sha256']==r.sha(src)==v['source_sha256'] and rc['objects']==ob,n
 assert n not in D['modules'],('unexpected nominal overlap',n)
 for dep,di in rc['key']['imports'].items():
  assert {k:z['sha256'] for k,z in D['modules'][dep]['objects'].items()}=={k:z['sha256'] for k,z in di['objects'].items()},('producing direct import differs',n,dep)
 D['modules'][n]={'root':'selected_current_215','source':str(src),'source_sha256':r.sha(src),'imports':r.imports(src,True),'objects':ob,'build_receipt':{'path':str(rp),'sha256':r.sha(rp)}};D['provenance_files'][str(rp)]=r.sha(rp);producing.append(n)
# Exact current recursive import identity, not merely equal direct object bytes.
keys=r.external_keys(D)
for n in producing:
 rc=json.loads((S/'successful-targets'/(n+'.json')).read_text())
 for dep,di in rc['key']['imports'].items():
  if 'closure_key' in di:assert keys[dep]==di['closure_key'],('producing recursive external import differs',n,dep)
  else:
   producer=json.loads((S/'successful-targets'/(dep+'.json')).read_text());assert di['receipt_key']==r.digest(producer['key']),('producing project key differs',n,dep)
assert not (W/'successful-targets').exists() or not list((W/'successful-targets').glob('*.json'));W.mkdir(exist_ok=True);(W/'sources').mkdir(exist_ok=True);shutil.copy2(S/'runner.py',W/'runner.py')
D['scope']='Current source-read proof snapshot: current215 selected-read refresh plus A current sampler snapshot. Exact common source/object/import identities and every selected project producing direct/recursive import checked; no historical project objects substituted.'
r.dump(W/'external-inputs.json',D);r.dump(W/'coherent-import-merge-audit.json',{'common_module_count':len(common),'common_modules':common,'fresh_selected_project_count':len(producing),'fresh_selected_modules':producing,'sampler_project_overlap':[],'source_selected_snapshot':str(S/'external-inputs.json'),'source_sampler_snapshot':str(A/'sampler-current-object-pins.json'),'recursive_producing_import_identity_checked':True,'no_historical_project_objects_adopted':True,'root_path_normalization':'A added-module root labels expanded to exact per-module source/object origins; hashes, names, declarations, imports and producing receipts unchanged. Original snapshot retained.'})
# Only the two changed/novel source files; no expanded theorem rebuild.
mods={}
for n in ['ExtractedSourceSemanticSampler','ExtractedSelectedSourceRecords']:
 src=S/'source-read-incoming'/(n+'.lean');assert src.is_file(),('copy incoming sources before staging',str(src))
 dest=W/'sources'/(n+'.lean');shutil.copy2(src,dest);mods[n]={'stage_as':n+'.lean','source_sha256':r.sha(dest),'imports':r.imports(dest),'source_revision':'a555c852664c80000942f0c911e16719a5493625','role':'Novel focused fixed source-to-selected bridge; each displayed export axiom audited'}
r.dump(W/'sources/SOURCE-MANIFEST.json',{'format':2,'modules':mods,'topological_order':list(mods),'groups':{'source-read':list(mods)}})
print(json.dumps({'workspace':str(W),'external_modules':len(D['modules']),'common_checked':len(common),'targets':list(mods)}))
