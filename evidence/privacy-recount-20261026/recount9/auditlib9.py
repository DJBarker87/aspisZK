from pathlib import Path
import json,re,subprocess,hashlib,os,collections,gzip
P=Path(__file__).resolve().parent;B=P.parent;pins=json.loads((P/'pins.json').read_text())['revisions']
bundles={}
manifest=json.loads((P/'manifest.json').read_text()) if (P/'manifest.json').exists() else [];ix={(x['ref'],x['path']):x for x in manifest}
def read(k,path):
 x=ix.get((k,path))
 if x:
  f=P/x['snapshot']
  if 'snapshot_key' in x:
   if str(f) not in bundles:bundles[str(f)]=json.loads(gzip.decompress(f.read_bytes()))
   return bundles[str(f)][x['snapshot_key']]
  return gzip.open(f,'rt').read() if f.suffix=='.gz' else f.read_text()
 q=subprocess.run(['git','show',pins[k]+':'+path],capture_output=True)
 if q.returncode:return None
 raw=q.stdout;blob=hashlib.sha1(b'blob '+str(len(raw)).encode()+b'\0'+raw).hexdigest();f=P/'objects'/(blob+'.txt');f.parent.mkdir(exist_ok=True);f.write_bytes(raw)
 x=dict(ref=k,revision=pins[k],path=path,blob=blob,sha256=hashlib.sha256(raw).hexdigest(),snapshot=os.path.relpath(f,P));ix[k,path]=x;manifest.append(x);return raw.decode()
def save(): (P/'manifest.json').write_text(json.dumps(manifest,indent=1)+'\n')
R='docs/research/v8-r0-zk-20261009/lean/'
resolved={}
def module(k,m):
 if (k,m) in resolved:return resolved[k,m]
 paths=[R+m.replace('.','/')+'.lean']
 if m.startswith('R1Z.ProverRwFull'):paths+=['docs/research/100bit-spend-path-20261013/lean/prover-rw-20261023/'+m.split('.')[-1]+'.lean']
 if m.startswith('PV_B3_'):paths+=['evidence/pv-batch3-20261027/lean/'+m+'.lean']
 if m.startswith('PV_B1_'):paths+=['evidence/pv-op254-20261027/lean/'+m+'.lean']
 if m.startswith('PV_B3P_'):paths+=['evidence/pv-b3p6-20261028/lean/'+m+'.lean']
 for path in paths:
  s=read(k,path)
  if s is not None:resolved[k,m]=(s,path);return s,path
 resolved[k,m]=(None,paths[0]);return None,paths[0]
