from pathlib import Path
import tarfile,json,hashlib,io
W=Path('/home/dombarker/project-offloads/aspis-r1-worker-c-verify-prefix-proof-20261017');names=['ExtractedDigest32Transcript','ExtractedDigest32Callers','ExtractedDigest32Begin','ExtractedSourceFull25Frames'];out=W/'source-full25-frames-accepted.tar.gz';items={}
def add(p,n):items[n]=p.read_bytes()
for n in names:
 for path,key in [(W/'sources'/(n+'.lean'),'sources/'+n+'.lean'),(W/'objects'/(n+'.olean'),'objects/'+n+'.olean'),(W/'successful-targets'/(n+'.json'),'successful-targets/'+n+'.json')]:add(path,key)
for run in (W/'runs').iterdir():
 if not run.name.startswith('source25-'):continue
 for p in run.rglob('*'):
  if p.is_file() and not p.is_symlink() and 'import-overlay' not in p.relative_to(run).parts:add(p,'runs/'+str(p.relative_to(W/'runs')))
for n in ['runner.py','serial-source25-host.py','serial-source25.log','external-inputs.json']:
 add(W/n,n)
add(W/'sources/SOURCE-MANIFEST.json','SOURCE-MANIFEST.json')
ss={n:hashlib.sha256(b).hexdigest() for n,b in items.items()};items['SHA256SUMS.json']=(json.dumps(ss,indent=2,sort_keys=True)+'\n').encode()
with tarfile.open(out,'w:gz') as t:
 for n,b in sorted(items.items()):
  f=tarfile.TarInfo(n);f.size=len(b);f.mode=0o644;f.mtime=0;t.addfile(f,io.BytesIO(b))
print(json.dumps({'archive':str(out),'sha256':hashlib.sha256(out.read_bytes()).hexdigest(),'bytes':out.stat().st_size,'members':len(items)}))
for n in names:
 d=json.loads((W/'successful-targets'/(n+'.json')).read_text());print(n,d['exit_status'],d['wall_seconds'],d['peak_process_rss_kib'],d['process_swaps'],d['axioms']['requested_count'])
