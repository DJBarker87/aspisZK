"""Read-only recovery of terminal compiled inputs; content addressed once."""
from pathlib import Path
import json,subprocess,base64,hashlib,lzma
E=Path(__file__).resolve().parent;B='/home/dombarker/project-offloads/codex-cx-pool-b3-20261106'
ids=[json.loads(l)['attempt'] for l in (E/'NHP_ATTEMPTS.jsonl').read_text().splitlines()]
code='''from pathlib import Path
import json,hashlib,base64
b=Path(B);rows=[];payloads={}
for a in ids:
 rc=json.loads((b/a/'receipt.json').read_text())
 for name,h in rc['source_hashes'].items():
  p=b/a/'sources'/name
  raw=p.read_bytes();assert hashlib.sha256(raw).hexdigest()==h,(a,name)
  payloads.setdefault(h,base64.b64encode(raw).decode())
  rows.append(dict(attempt=a,name=name,sha256=h,bytes=len(raw)))
print(json.dumps(dict(rows=rows,payloads=payloads)))
'''
r=subprocess.run(['ssh','-o','ControlMaster=no','-o','ConnectTimeout=15','dombarker@100.108.41.90','python3'],input='B='+repr(B)+'\nids='+repr(ids)+'\n'+code,text=True,capture_output=True)
(E/'NHP_SOURCE_COLLECTION.log').write_text(r.stderr);assert r.returncode==0,(r.returncode,r.stderr)
x=json.loads(r.stdout);store=E/'NHP_pinned_inputs';store.mkdir(exist_ok=True)
for h,b64 in x['payloads'].items():
 raw=base64.b64decode(b64);assert hashlib.sha256(raw).hexdigest()==h
 dest=store/(h+'.xz')
 if dest.exists():assert lzma.decompress(dest.read_bytes())==raw
 else:dest.write_bytes(lzma.compress(raw,preset=6))
for row in x['rows']:
 p=E/row['attempt']/'sources'/row['name'];p.parent.mkdir(parents=True,exist_ok=True)
 if p.exists():assert hashlib.sha256(p.read_bytes()).hexdigest()==row['sha256'];p.unlink()
 p.with_name(p.name+'.REFERENCE.json').write_text(json.dumps(dict(sha256=row['sha256'],bytes=row['bytes'],compressed='NHP_pinned_inputs/'+row['sha256']+'.xz'),indent=1)+'\n')
(E/'NHP_COMPILED_INPUTS.json').write_text(json.dumps(dict(rows=x['rows'],unique_inputs=len(x['payloads']),compressed_bytes=sum(p.stat().st_size for p in store.glob('*.xz'))),indent=1)+'\n')
print(json.dumps(dict(terminal_attempts=len(ids),snapshots=len(x['rows']),unique_inputs=len(x['payloads']))))
