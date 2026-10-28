from pathlib import Path
import json,sys,shlex,subprocess
E=Path(__file__).resolve().parent;sys.path.insert(0,str(E));import KDX_host as h
rows=json.loads((E/'KDX_PASS_INVENTORY.json').read_text());requests=[]
for row in rows:
 cmd=row['command']
 if '--manifest-path' not in cmd:continue
 manifest=Path(cmd[cmd.index('--manifest-path')+1]);parts=manifest.parts
 if 'crates' in parts and manifest.is_absolute():base=Path(*parts[:parts.index('crates')-1])
 else:
  env=row.get('env') or {}; tmp=env.get('TMPDIR') or env.get('CARGO_TARGET_DIR')
  if not tmp:continue
  base=Path(tmp).parent
 attempt=Path(row['receipt']).parent.name
 for name,sha in (row.get('source_hashes') or {}).items():
  if not name.endswith('.rs'):continue
  requests.append(dict(path=str(base/attempt/'sources'/name),sha256=sha,receipt=row['receipt']))
code='''from pathlib import Path
import json,hashlib
out={};missing=[]
for q in REQUESTS:
 p=Path(q['path'])
 if not p.is_file():missing.append(q);continue
 s=p.read_text();sha=hashlib.sha256(p.read_bytes()).hexdigest()
 assert sha==q['sha256'],q
 out[sha]=dict(path=str(p),text=s)
print(json.dumps(dict(sources=out,missing=missing)))
'''.replace('REQUESTS',repr(requests))
(E/'KDX_fetch_host.py').write_text(code)
h.admit('KDX_FETCH')
r=subprocess.run(['scp',str(E/'KDX_fetch_host.py'),h.H+':'+h.B+'/KDX_fetch_host.py'],capture_output=True,text=True);assert r.returncode==0,r.stderr
r=h.ssh('python3 '+h.B+'/KDX_fetch_host.py');assert r.returncode==0,r.stderr
d=json.loads(r.stdout)
for row in rows:
 for name,sha in (row.get('source_hashes') or {}).items():
  p=E.parents[1]/Path(row['receipt']).parent/'sources'/name
  if name.endswith('.rs') and sha not in d['sources'] and p.is_file():
   import hashlib
   assert hashlib.sha256(p.read_bytes()).hexdigest()==sha
   d['sources'][sha]=dict(path=str(p),text=p.read_text())
(E/'KDX_SOURCE_SNAPSHOTS.json').write_text(json.dumps(d))
print('sources',len(d['sources']),'missing',len(d['missing']))
