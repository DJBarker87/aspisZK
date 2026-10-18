from pathlib import Path
import tarfile,json,hashlib,io
W=Path('/home/dombarker/project-offloads/aspis-r1-worker-c-source-read-proof-20261018')
sha=lambda p:hashlib.file_digest(p.open('rb'),'sha256').hexdigest()
rs=[json.loads(p.read_text()) for p in sorted((W/'successful-targets').glob('*.json'))]
assert len(rs)==2 and all(r['axioms']['passed'] and r['exit_status']==0 and r['process_swaps']==0 for r in rs)
items={}
for root in ['sources','objects','successful-targets','runs']:
 for p in (W/root).rglob('*'):
  if not p.is_file() or p.is_symlink() or any(x in {'import-overlay','__pycache__'} for x in p.relative_to(W).parts):continue
  # The deterministic symlink journal repeats the entire pinned closure for
  # each attempt; the runner plus snapshot reproduce it without missing bytes.
  if p.name=='import-overlay-links.jsonl':continue
  items[str(p.relative_to(W))]=p
for p in W.iterdir():
 if p.is_file() and p.suffix in {'.py','.json','.log'} and p.name not in {'packet-manifest.json'}:items[p.name]=p
records={n:sha(p) for n,p in items.items()};sums=(json.dumps(records,indent=2,sort_keys=True)+'\n').encode()
out=W/'source-read-current-accepted.tar.gz'
with tarfile.open(out,'w:gz') as t:
 for n,p in sorted(items.items()):
  ti=t.gettarinfo(str(p),arcname=n);ti.mtime=0;ti.uid=ti.gid=0;ti.uname=ti.gname='';ti.mode=0o644
  with p.open('rb') as f:t.addfile(ti,f)
 ti=tarfile.TarInfo('SHA256SUMS.json');ti.size=len(sums);ti.mtime=0;ti.mode=0o644;t.addfile(ti,io.BytesIO(sums))
manifest={'archive':out.name,'archive_sha256':sha(out),'archive_bytes':out.stat().st_size,'members':len(items)+1,'targets':len(rs),'axiom_reports':sum(len(r['axioms']['reports']) for r in rs),'compile_only_targets':[r['target'] for r in rs if not r['axioms']['requested_count']],'maximum_process_rss_kib':max(r['peak_process_rss_kib'] for r in rs),'swaps':sum(r['process_swaps'] for r in rs),'scope':'Two focused current source bridges: fixed actual sampler→existing QM31Exact/WideExact semChal and source25 bounded selected records/strict decoder→hread. Empty table plus explicit oracle/callback does not claim actual completed q agreement, typed log recovery or custody. Exact current215+sampler common source/object/recursive producing imports audited; metadata-only root/implicit Init normalization retained with original rejected preflights. No historical RawCut imports.','metrics':[{'target':r['target'],'exit_status':r['exit_status'],'wall_seconds':r['wall_seconds'],'peak_process_rss_kib':r['peak_process_rss_kib'],'swaps':r['process_swaps'],'revision':r['source_revision'],'axioms':r['axioms']} for r in rs]}
(W/'packet-manifest.json').write_text(json.dumps(manifest,indent=2,sort_keys=True)+'\n');print(json.dumps({k:v for k,v in manifest.items() if k!='metrics'}))
