from pathlib import Path
import json,hashlib,tarfile,io
W=Path('/home/dombarker/project-offloads/aspis-r1-worker-c-source-trace-proof-20261018');O=Path('/home/dombarker/project-offloads/aspis-r1-j17-port-20261015/bridge/sources');sha=lambda p:hashlib.file_digest(p.open('rb'),'sha256').hexdigest();rs=[json.loads(p.read_text()) for p in(W/'successful-targets').glob('*.json')];selected={'R1UnifiedSemanticRecoveryCore','R1PublicInitBoundaryFacts','R1InitialWalkCells','R1DuplexRecordPrefix','R1InitialWalkTrace','TraceAppend','ExtractedSourceDigestOracle'};rs=[r for r in rs if r['target'] in selected];assert len(rs)==7 and all(r['exit_status']==0 and r['axioms']['passed'] for r in rs)
m=json.loads((W/'sources/SOURCE-MANIFEST.json').read_text());m['modules']={n:v for n,v in m['modules'].items() if n in selected};m['topological_order']=[n for n in m['topological_order'] if n in selected];m['groups']={k:[n for n in v if n in selected] for k,v in m['groups'].items()};virtual={'sources/SOURCE-MANIFEST.json':(json.dumps(m,indent=2,sort_keys=True)+'\n').encode()}
original=(O/'R1UnifiedSemanticRecovery.lean').read_text();at=original.index('def typed ');end=original.index('\ntheorem typed_before_row',at);core=(W/'sources/R1UnifiedSemanticRecoveryCore.lean').read_text();ca=core.index('def typed ');ce=core.index('\n#print axioms',ca);assert original[at:end].strip()==core[ca:ce].strip()
context={'original_namespace_context':original[:at],'new_core_context':core[:ca],'exact_definition_statement_and_body_equal':True,'qualified_declaration':'AspisR1.UnifiedSemanticRecovery.typed','original_section_variable_context':'{M Cv W : Type} {L : Nat}; W unused by typed and not a declaration binder','new_section_variable_context':'{M Cv : Type} {L : Nat}','same_required_opens':['FS','FS2','FS2.Duplex','AspisV8PairedCommitment','AspisV8R19.DuplexFrames','AspisV8R19.SourceDuplexStep'],'elaborated_compilation_and_standard_axioms_required':True,'notes':'Original broad probability/model imports and extra opens are not needed by the exact parser declaration. Compilation resolves the same Params, Table, State, Bytes, Rec, InitialWalk.walk and RawRoundDecode.decode. Companion full module remains source-only inverse artifact.'};virtual['typed-core-context-audit.json']=(json.dumps(context,indent=2,sort_keys=True)+'\n').encode();virtual['original-context/R1UnifiedSemanticRecovery.lean']=original.encode()
items={}
for root in ['sources','objects','successful-targets','runs','split-sources']:
 for p in(W/root).rglob('*'):
  rel=p.relative_to(W)
  if not p.is_file() or p.is_symlink() or any(v in {'import-overlay','__pycache__'} for v in rel.parts) or p.name=='import-overlay-links.jsonl':continue
  if str(rel) in virtual:continue
  if root=='runs' and rel.parts[1].startswith('source-agreement'):continue
  if root=='sources' and p.suffix=='.lean' and str(rel)[8:-5].replace('/','.') not in selected:continue
  if root=='objects' and not any(str(rel).startswith('objects/'+n.replace('.','/')+'.') for n in selected):continue
  if root=='successful-targets' and p.stem not in selected:continue
  items[str(rel)]=p
for p in W.iterdir():
 if p.is_file() and p.suffix in {'.py','.json','.log'} and not p.name.startswith(('packet-','serial-source-agreement','preflight-agreement','launch-agreement','append-agreement')):items[p.name]=p
records={n:sha(p) for n,p in items.items()};records.update({n:hashlib.sha256(b).hexdigest() for n,b in virtual.items()});virtual['SHA256SUMS.json']=(json.dumps(records,indent=2,sort_keys=True)+'\n').encode();out=W/'source-trace-prerequisites-accepted.tar.gz'
with tarfile.open(out,'w:gz') as t:
 for n in sorted(set(items)|set(virtual)):
  if n in virtual:
   b=virtual[n];ti=tarfile.TarInfo(n);ti.size=len(b);ti.mode=0o644;ti.mtime=0;t.addfile(ti,io.BytesIO(b))
  else:
   p=items[n];ti=t.gettarinfo(str(p),arcname=n);ti.mtime=0;ti.uid=ti.gid=0;ti.uname=ti.gname=''
   with p.open('rb') as f:t.addfile(ti,f)
manifest={'archive':out.name,'archive_sha256':sha(out),'archive_bytes':out.stat().st_size,'members':len(records)+1,'targets':len(rs),'axiom_reports':sum(len(r['axioms']['reports']) for r in rs),'maximum_process_rss_kib':max(r['peak_process_rss_kib'] for r in rs),'swaps':sum(r['process_swaps'] for r in rs),'scope':'Six small current generic/core trace-recovery prerequisites plus actual D-derived oracle. No SHA distribution/custody/whole-runtime table premise is concluded. Exact typed declaration split includes complete original namespace/section/open context and inverse companion audit. SourceAgreement is subsequent separate work, excluded from release targets.','metrics':[{'target':r['target'],'exit_status':r['exit_status'],'wall_seconds':r['wall_seconds'],'peak_process_rss_kib':r['peak_process_rss_kib'],'swaps':r['process_swaps'],'revision':r['source_revision'],'axioms':r['axioms']} for r in rs]};(W/'packet-prerequisites-manifest.json').write_text(json.dumps(manifest,indent=2,sort_keys=True)+'\n');print(json.dumps({k:v for k,v in manifest.items() if k!='metrics'}))
