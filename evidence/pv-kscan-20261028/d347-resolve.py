from pathlib import Path
import json,subprocess,re,hashlib,collections
C=Path('/private/tmp/pv-kscan-cache-20261028');E=Path(__file__).resolve().parent;db=json.loads((C/'d347-source-db.json').read_text());ps=json.loads((E/'d347-input.json').read_text())['passes'];rs=json.loads((C/'d347-receipts.json').read_text());cache={};attempts=0;found=0
for p in ps:
 r=rs[p['receipt_blob']];r=r if isinstance(r,dict) else {};rev=re.match('[0-9a-f]{10,40}',p['source_revision'] or '')
 if not rev:continue
 rev=rev[0]
 for k in ['source_sha256','inputs','source_hashes','source_snapshots']:
  m=r.get(k)
  if not isinstance(m,dict):continue
  for path,h in m.items():
   if isinstance(h,dict):h=h.get('sha256')
   if h in db or not isinstance(h,str) or not path.endswith(('.rs','Cargo.toml','Cargo.lock')):continue
   rel=path
   if '/source/' in path:rel=path.split('/source/',1)[1]
   elif '/step-proof/' in path:rel='tools/pv-cb-20261026/step-proof/'+path.split('/step-proof/',1)[1]
   elif path.startswith('/'):continue
   pair=(rev,rel)
   if pair in cache:continue
   attempts+=1;v=subprocess.run(['git','show',rev+':'+rel],capture_output=True)
   cache[pair]=True
   if v.returncode==0:
    sha=hashlib.sha256(v.stdout).hexdigest()
    db.setdefault(sha,dict(text=v.stdout.decode(),origin=rev+':'+rel,kind='git original revision'))
    if sha==h:found+=1
(C/'d347-source-db.json').write_text(json.dumps(db));print('git probes',attempts,'exact hashes recovered',found)
for i in [111,114,115,130,132,133,149,151,153,154,156,158,197,203,218,223,225,231,243,245,259]:
 p=next(p for p in ps if p['index']==i);r=rs[p['receipt_blob']];m=r.get('source_sha256',{});m=m if isinstance(m,dict) else {};miss=[f for f,h in m.items() if h not in db and (f.endswith('.rs') or f.endswith('Cargo.toml') or f.endswith('Cargo.lock')) and f.startswith(('crates/','Cargo','tools/prover-rw-20261023/pv-rw'))];print(i,'missing',len(miss),miss[:8])
