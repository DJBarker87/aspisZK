from pathlib import Path
import json,hashlib,tarfile,io,importlib.util
W=Path('/home/dombarker/project-offloads/aspis-r1-worker-c-source-trace-proof-20261018');sp=importlib.util.spec_from_file_location('r',W/'runner.py');r=importlib.util.module_from_spec(sp);sp.loader.exec_module(r)
new={'ExtractedSourceTypedRecords','ExtractedSourceTypedRecovery','ExtractedSourceObservations','ExtractedSourceCanonicalRecovery','ExtractedSourceFirstTyped'};previous={'ExtractedSelectedSourceAgreement','ExtractedSourceTraceIndices','ExtractedSourceReadFromFirst','R1UnifiedSemanticRecoveryCore','R1PublicInitBoundaryFacts','R1InitialWalkCells','R1DuplexRecordPrefix','R1InitialWalkTrace','TraceAppend','ExtractedSourceDigestOracle'};allnames=new|previous;rs={n:json.loads((W/'successful-targets'/(n+'.json')).read_text()) for n in allnames};assert all(v['exit_status']==0 and v['axioms']['passed'] and not v['process_swaps'] for v in rs.values())
m=r.staged(W);D=json.loads((W/'external-inputs.json').read_text());oldkeys=r.external_keys(D);D['roots'].append({'name':'current_source_trace_checkpoint','source':str(W/'sources'),'objects':str(W/'objects')})
for n in m['topological_order']:
 if n not in allnames:continue
 rc=rs[n];src=W/'sources'/m['modules'][n]['stage_as'];ob=r.object_pins(W/'objects',n,D['olean_header_seal']);assert rc['key']['source_sha256']==r.sha(src) and rc['objects']==ob
 for dep,pin in rc['key']['imports'].items():
  if dep in rs:assert pin['receipt_key']==r.digest(rs[dep]['key'])
  else:assert oldkeys[dep]==pin['closure_key']
 rp=W/'successful-targets'/(n+'.json');D['modules'][n]={'root':'current_source_trace_checkpoint','source':str(src),'source_sha256':r.sha(src),'imports':r.imports(src,True),'objects':ob,'build_receipt':{'path':str(rp),'sha256':r.sha(rp)}};D['provenance_files'][str(rp)]=r.sha(rp)
virtual={'current-object-pins.json':(json.dumps(D,indent=2,sort_keys=True)+'\n').encode(),'accepted-project-predecessors.json':(json.dumps({'prior_archives':['7dbd428c81ee45c8aa631e75b075cbed7cac472c6fc559709cae65a556e3de65','bc700a9bb9e352f529ed4fd87123699a8fc4b7a56cc789384efba0646ef05409'],'receipts':{n:rs[n] for n in sorted(previous)}},indent=2,sort_keys=True)+'\n').encode()}
mm=json.loads(json.dumps(m));mm['modules']={n:v for n,v in mm['modules'].items() if n in new};mm['topological_order']=[n for n in mm['topological_order'] if n in new];mm['groups']={'new-source-read':mm['topological_order']};virtual['sources/SOURCE-MANIFEST.json']=(json.dumps(mm,indent=2,sort_keys=True)+'\n').encode();items={}
for root in ['sources','objects','successful-targets','runs']:
 for p in(W/root).rglob('*'):
  rel=p.relative_to(W)
  if not p.is_file() or p.is_symlink() or any(v in {'import-overlay','__pycache__'} for v in rel.parts) or p.name=='import-overlay-links.jsonl' or str(rel) in virtual:continue
  if root=='runs' and not rel.parts[1].startswith(('source-typed-records-','source-typed-recovery-','source-observations-','source-canonical-recovery-','source-first-typed-')):continue
  if root=='sources' and p.suffix=='.lean' and str(rel)[8:-5].replace('/','.') not in new:continue
  if root=='objects' and not any(str(rel).startswith('objects/'+n+'.') for n in new):continue
  if root=='successful-targets' and p.stem not in new:continue
  items[str(rel)]=p
for p in W.iterdir():
 if p.is_file() and p.suffix in {'.py','.json','.log'} and not p.name.startswith(('packet-','serial-source-trace','serial-source-typed')):items[p.name]=p
sums={n:r.sha(p) for n,p in items.items()};sums.update({n:hashlib.sha256(b).hexdigest() for n,b in virtual.items()});virtual['SHA256SUMS.json']=(json.dumps(sums,indent=2,sort_keys=True)+'\n').encode();out=W/'source-typed-actual-first-accepted.tar.gz'
with tarfile.open(out,'w:gz') as t:
 for n in sorted(set(items)|set(virtual)):
  if n in virtual:
   b=virtual[n];ti=tarfile.TarInfo(n);ti.size=len(b);ti.mode=0o644;ti.mtime=0;t.addfile(ti,io.BytesIO(b))
  else:
   p=items[n];ti=t.gettarinfo(str(p),arcname=n);ti.mtime=0;ti.uid=ti.gid=0;ti.uname=ti.gname=''
   with p.open('rb') as f:t.addfile(ti,f)
manifest={'archive':out.name,'archive_sha256':r.sha(out),'archive_bytes':out.stat().st_size,'members':len(sums)+1,'targets':len(new),'axiom_reports':sum(len(rs[n]['axioms']['reports']) for n in new),'maximum_process_rss_kib':max(rs[n]['peak_process_rss_kib'] for n in new),'swaps':sum(rs[n]['process_swaps'] for n in new),'current_snapshot_modules':len(D['modules']),'accepted_previous_targets':len(previous),'scope':'Actual first same-witness constructor, source25 run and row25 absorb derive canonical77 relevant observations, ha and nohit-conditional htyped on the same table. Whole experiment embedding remains explicit observation inclusion, consistency, budget and nohit; no runtime583-call equality or literal C1/C2 word/context custody claim. Stronger current recovery counted once; older successful weaker recovery retained as superseded diagnostic.','metrics':[{'target':rs[n]['target'],'exit_status':rs[n]['exit_status'],'wall_seconds':rs[n]['wall_seconds'],'peak_process_rss_kib':rs[n]['peak_process_rss_kib'],'swaps':rs[n]['process_swaps'],'revision':rs[n]['source_revision'],'axioms':rs[n]['axioms']} for n in sorted(new)]};r.dump(W/'packet-source-typed-manifest.json',manifest);r.dump(W/'current-object-pins.json',D);print(json.dumps({k:v for k,v in manifest.items() if k!='metrics'}))
