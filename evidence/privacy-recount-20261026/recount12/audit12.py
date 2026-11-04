"""Read immutable Git objects only. No proof, compiler, extractor or Kani launches."""
import json,subprocess,hashlib,gzip,lzma,re,collections,base64
from pathlib import Path
P=Path(__file__).resolve().parent; B=P.parent
pins=json.loads((P/'pins.json').read_text()); revs=pins['revisions']; manifest={}; cache={}; trees={}
def git(*a):return subprocess.check_output(['git',*a])
def tree(k):
 if k not in trees:trees[k]=git('ls-tree','-r','--name-only',revs.get(k,k)).decode().splitlines()
 return trees[k]
def read(k,path):
 key=(k,path)
 if key in cache:return cache[key]
 revision=revs.get(k,k)
 old=manifest.get(k+':'+path)
 if old and old['revision']==revision and old.get('snapshot') and (P/old['snapshot']).exists():
  data=(P/old['snapshot']).read_bytes()
  if old.get('snapshot_key'):
   v=json.loads(lzma.decompress(data))[old['snapshot_key']]
   b=v['data'].encode() if v['encoding']=='utf8' else base64.b64decode(v['data'])
  else:b=gzip.decompress(data)
  cache[key]=b;return b
 if path not in tree(k):cache[key]=None;return None
 b=git('show',revision+':'+path);h=hashlib.sha256(b).hexdigest();snap='objects/'+h+'.gz'
 (P/'objects').mkdir(exist_ok=True)
 if not (P/snap).exists():(P/snap).write_bytes(gzip.compress(b,mtime=0))
 manifest[k+':'+path]={'ref':k,'revision':revision,'path':path,'sha256':h,'bytes':len(b),'snapshot':snap}
 cache[key]=b;return b
def txt(k,path):
 b=read(k,path);return b.decode() if b is not None else None
resolved={}
def module(k,m):
 if (k,m) in resolved:return resolved[k,m]
 known=[]
 if m.startswith('R1Z.ProverRwFull'):known.append('docs/research/100bit-spend-path-20261013/lean/prover-rw-20261023/'+m.split('.')[-1]+'.lean')
 if m.startswith('PV_B3P_'):known.append('evidence/pv-b3p6-20261028/lean/'+m+'.lean')
 known.append('lean/'+m.replace('.','/')+'.lean')
 for q in known:
  if q in tree(k):
   ans=(txt(k,q),q);resolved[k,m]=ans;return ans
 p='docs/research/v8-r0-zk-20261009/lean/'+m.replace('.','/')+'.lean'
 if p not in tree(k):
  opts=[s for s in tree(k) if s.endswith('/'+m.replace('.','/')+'.lean') or s==m.replace('.','/')+'.lean']
  if not opts:opts=[s for s in tree(k) if s.endswith('/'+m.split('.')[-1]+'.lean')]
  if len(opts)!=1:return None,None
  p=opts[0]
 ans=(txt(k,p),p);resolved[k,m]=ans;return ans
def save(): (P/'manifest.json').write_text(json.dumps(list(manifest.values()),indent=1)+'\n')
