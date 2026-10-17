from pathlib import Path
import tarfile,json,hashlib,io
W=Path('/home/dombarker/project-offloads/aspis-r1-worker-c-finish-a555-proof-20261017');out=W/'finish-actual25-accepted.tar.gz';items={}
for root in ['sources','objects','successful-targets','runs','fixed-rounds-generated']:
 for p in (W/root).rglob('*'):
  if not p.is_file() or p.is_symlink() or any(x in {'import-overlay','__pycache__'} for x in p.relative_to(W).parts):continue
  items[str(p.relative_to(W))]=p.read_bytes()
for p in W.iterdir():
 if p.is_file() and p.suffix in {'.py','.json','.log'}:items[p.name]=p.read_bytes()
E=Path('/home/dombarker/project-offloads/aspis-r1-worker-a-finish-a555-20261017')
for p in E.rglob('*'):
 if not p.is_file() or p.is_symlink() or any(x in {'target','.lake','__pycache__'} for x in p.relative_to(E).parts) or p.suffix=='.gz':continue
 items['finish-extraction/'+str(p.relative_to(E))]=p.read_bytes()
A=Path('/home/dombarker/project-offloads/aspis-r1-worker-a-rounds-proof-20261017')
for n,run in [('ExtractedSemanticRoundsModel','model-d'),('ExtractedSemanticRoundsReachability','reach-d')]:
 for p in [A/'sources'/(n+'.lean'),A/'objects'/(n+'.olean')]:items['rounds-predecessor/'+str(p.relative_to(A))]=p.read_bytes()
 for p in (A/'runs'/run).iterdir():
  if p.is_file():items['rounds-predecessor/'+str(p.relative_to(A))]=p.read_bytes()
records={n:hashlib.sha256(b).hexdigest() for n,b in items.items()};items['SHA256SUMS.json']=(json.dumps(records,indent=2,sort_keys=True)+'\n').encode()
with tarfile.open(out,'w:gz') as t:
 for n,b in sorted(items.items()):
  ti=tarfile.TarInfo(n);ti.size=len(b);ti.mtime=0;ti.mode=0o644;t.addfile(ti,io.BytesIO(b))
rs=[json.loads(b) for n,b in items.items() if n.startswith('successful-targets/')];assert len(rs)==3 and all(r['axioms']['passed'] and r['exit_status']==0 for r in rs)
manifest={'archive':out.name,'archive_sha256':hashlib.sha256(out.read_bytes()).hexdigest(),'archive_bytes':out.stat().st_size,'members':len(items),'targets':len(rs),'axiom_reports':sum(len(r['axioms']['reports']) for r in rs),'metrics':[{'target':r['target'],'exit_status':r['exit_status'],'wall_seconds':r['wall_seconds'],'peak_process_rss_kib':r['peak_process_rss_kib'],'swaps':r['process_swaps'],'revision':r['source_revision'],'axioms':r['axioms']} for r in rs]};(W/'packet-manifest.json').write_text(json.dumps(manifest,indent=2,sort_keys=True)+'\n');print(json.dumps({k:v for k,v in manifest.items() if k!='metrics'}))
