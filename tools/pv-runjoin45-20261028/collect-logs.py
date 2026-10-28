"""Collect immutable original per-module output/time logs, compressed with hashes."""
from pathlib import Path
import json,subprocess,shlex,lzma,hashlib,time
R=Path(__file__).resolve().parents[2];E=R/'evidence/pv-runjoin45-20261028';rows=[v for p in sorted(E.glob('modules-*.json')) for v in json.loads(p.read_text())]
request=[dict(module=v['module'],output_path=v['output_path'],output_sha256=v['output_sha256'],time_path=v['time_path'],time_sha256=v['time_sha256']) for v in rows]
code=r'''import json,pathlib,sys,hashlib,lzma
rows=json.load(sys.stdin);out=[]
for v in rows:
 x=v.copy()
 for k in ['output','time']:
  b=pathlib.Path(v[k+'_path']).read_bytes();assert hashlib.sha256(b).hexdigest()==v[k+'_sha256'],v[k+'_path'];x[k]=b.decode()
 out.append(x)
sys.stdout.buffer.write(lzma.compress(json.dumps(out).encode(),preset=6))'''
for k in range(11):
 r=subprocess.run(['ssh','dombarker@100.108.41.90','python3 -c '+shlex.quote(code)],input=json.dumps(request).encode(),capture_output=True)
 if r.returncode!=255:break
 if k==10:raise RuntimeError('ten transport retries exhausted; logs retained on host')
 print('collection transport cooldown60s; never recompile',flush=True);time.sleep(60)
assert r.returncode==0,r.stderr.decode();b=lzma.decompress(r.stdout);out=json.loads(b);assert len(out)==len(request)
for x,w in zip(out,request):
 assert x['module']==w['module']
 for n in ['output','time']:assert hashlib.sha256(x[n].encode()).hexdigest()==w[n+'_sha256']
(E/'original-module-logs.json.xz').write_bytes(r.stdout);(E/'original-module-logs.json.sha256').write_text(hashlib.sha256(b).hexdigest()+'  original-module-logs.json\n')
(E/'original-log-integrity.json').write_text(json.dumps(dict(modules=len(out),logs=2*len(out),all_match=True,uncompressed_bytes=len(b),compressed_bytes=len(r.stdout),sha256=hashlib.sha256(b).hexdigest()),indent=2)+'\n')
print('collected',len(out),'module log pairs; all original hashes match')
