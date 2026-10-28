from pathlib import Path
import json,re,subprocess,hashlib,os,collections
P=Path(__file__).resolve().parent;B=P.parent;pins=json.loads((P/'pins.json').read_text())['revisions']
manifest=json.loads((P/'manifest.json').read_text());ix={(x['ref'],x['path']):x for x in manifest};used=set()
def read(k,path):
 used.add((k,path)); x=ix.get((k,path))
 if x:return (P/x['snapshot']).read_text()
 q=subprocess.run(['git','show',pins[k]+':'+path],capture_output=True)
 if q.returncode:return None
 raw=q.stdout;blob=hashlib.sha1(b'blob '+str(len(raw)).encode()+b'\0'+raw).hexdigest();f=P/'objects'/(blob+'.txt');f.parent.mkdir(exist_ok=True);f.write_bytes(raw)
 x=dict(ref=k,revision=pins[k],path=path,blob=blob,sha256=hashlib.sha256(raw).hexdigest(),snapshot=os.path.relpath(f,P));ix[k,path]=x;manifest.append(x);return raw.decode()
R='docs/research/v8-r0-zk-20261009/lean/'
resolved={}
def module(k,m):
 if (k,m) in resolved:return resolved[k,m]
 paths=[R+m.replace('.','/')+'.lean']
 if m.startswith('R1Z.ProverRwFull'):paths+=['docs/research/100bit-spend-path-20261013/lean/prover-rw-20261023/'+m.split('.')[-1]+'.lean']
 if m.startswith('PV_B3_'):paths+=['evidence/pv-batch3-20261027/lean/'+m+'.lean']
 if m.startswith('PV_B1_'):paths+=['evidence/pv-op254-20261027/lean/'+m+'.lean']
 for path in paths:
  s=read(k,path)
  if s is not None:resolved[k,m]=(s,path);return s,path
 resolved[k,m]=(None,paths[0]);return None,paths[0]
