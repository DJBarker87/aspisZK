from pathlib import Path
import json,sys,hashlib
E=Path(__file__).resolve().parent;sys.path.insert(0,str(E));import KMX_host as h
rows=json.loads((E.parent/'kani-diag-20261027/KDX_PASS_INVENTORY.json').read_text())
ex={r['id'] for r in json.loads((E.parent/'kani-diag-20261027/KDX_EXPOSURE.json').read_text())}
requests=[];sources=json.loads((E/'KMX_local_snapshots.json').read_text())['sources']
for row in rows:
 if Path(row['receipt']).parent.name not in ex:continue
 cmd=row['command']
 if '--manifest-path' not in cmd:continue
 manifest=Path(cmd[cmd.index('--manifest-path')+1]);parts=manifest.parts
 if 'crates' not in parts or not manifest.is_absolute():continue
 base=Path(*parts[:parts.index('crates')-1]);a=Path(row['receipt']).parent.name
 for name,sha in row.get('source_hashes',{}).items():
  if not name.endswith('.rs') or sha in sources:continue
  requests.append({'path':str(base/a/'sources'/name),'sha256':sha})
h.admit('KMX_FETCH')
missing=[]
for start in range(0,len(requests),20):
 r=h.remote_py('''from pathlib import Path
import json,hashlib
out={};missing=[]
for q in '''+repr(requests[start:start+20])+''':
 p=Path(q['path'])
 if not p.is_file():missing.append(q);continue
 assert hashlib.sha256(p.read_bytes()).hexdigest()==q['sha256'],q
 out[q['sha256']]={'path':str(p),'text':p.read_text()}
print(json.dumps({'sources':out,'missing':missing}))
''')
 assert r.returncode==0,r.stderr
 x=json.loads(r.stdout);sources.update(x['sources']);missing.extend(x['missing'])
x={'sources':sources,'missing':missing}
(E/'KMX_source_snapshots.json').write_text(json.dumps(x))
print('source snapshots',len(sources),'missing',len(x['missing']))
