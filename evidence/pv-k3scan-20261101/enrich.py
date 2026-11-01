import json,subprocess,pathlib,re,hashlib
E=pathlib.Path(__file__).resolve().parent
rs=json.loads((E/'RECOVERED.json').read_text());idx=json.loads((E/'SOURCE_INDEX.json').read_text());B=E/'blobs';cache={}
def get(rev,p):
 key=(rev,p)
 if key not in cache:
  r=subprocess.run(['git','show',rev+':'+p],capture_output=True);cache[key]=r.stdout if r.returncode==0 else None
 return cache[key]
def addsource(rev,p,b):
 h=hashlib.sha256(b).hexdigest();idx.setdefault(h,[]).append(dict(revision=rev,path=p));(B/(h+'.rs')).write_bytes(b)
def hashes(d):
 o={}
 if isinstance(d,dict):
  n=d.get('path',d.get('source',d.get('file')));h=d.get('sha256',d.get('source_sha256'))
  if isinstance(n,str) and n.endswith(('.rs','.rs.txt')) and isinstance(h,str) and len(h)==64:o[n]=h
  for n,v in d.items():
   h=v.get('sha256') if isinstance(v,dict) else v
   if isinstance(n,str) and n.endswith(('.rs','.rs.txt')) and isinstance(h,str) and len(h)==64:o[n]=h
   if isinstance(v,(dict,list)):o.update(hashes(v))
 elif isinstance(d,list):
  for v in d:o.update(hashes(v))
 return o
# Add Kani receipts named resumeN rather than kaniN; they were not in lexical discovery.
ref='codex/pv-cblib-20261027';rev=json.loads((E/'PINS.json').read_text())['pins'][ref]
ns=subprocess.check_output(['git','ls-tree','-r','--name-only',rev,'evidence/pv-cblib-20261027']).decode().splitlines()
known={r['path'] for r in rs}
for p in ns:
 if not p.endswith('collected-receipt.json') or p in known:continue
 b=get(rev,p)
 try:d=json.loads(b)
 except:continue
 if isinstance(d,dict) and 'kani' in json.dumps(d.get('target',[])):
  h=hashlib.sha256(b).hexdigest();(B/(h+'.json')).write_bytes(b);rs.append(dict(branch=ref,revision=rev,path=p,sha256=h,receipt=d))
for x in rs:
 r=x['receipt']
 if not isinstance(r,dict):continue
 rev=x['revision'];p=pathlib.PurePosixPath(x['path']);hh=x.get('recorded_rust_hashes',{})|hashes(r);side=[]
 names=['source-manifest.json','source-pins.json','inputs.json','source-hashes.json']
 for name in names:
  q=str(p.parent/name);b=get(rev,q)
  if b:
   try:d=json.loads(b)
   except:continue
   hh.update(hashes(d));side.append(q);(B/(hashlib.sha256(b).hexdigest()+'.json')).write_bytes(b)
 m=re.search(r'/(K\d+)/(?:receipt/)?[^/]*receipt.json$',str(p))
 if m:
  q=str(p).split('/'+m[1]+'/')[0]+'/'+m[1]+'-inputs.json';b=get(rev,q)
  if b:
   d=json.loads(b);hh.update(hashes(d));side.append(q);(B/(hashlib.sha256(b).hexdigest()+'.json')).write_bytes(b)
 # exact sidecar-recorded source only; no substitution of current same-name bytes
 for n,h in hh.items():
  if h in idx:continue
  path=re.search(r'(?:^|/)((?:tools|crates|programs)/.*\.rs)$',n);npath=path[1] if path else n
  for rr in [r.get('source_revision'),r.get('revision'),rev]:
   if not isinstance(rr,str):continue
   b=get(rr,npath)
   if b is not None and hashlib.sha256(b).hexdigest()==h:addsource(rr,npath,b);break
 x.update(recorded_rust_hashes=hh,sidecars=side,matched_rust={n:{'sha256':h,'provenance':idx[h][0]} for n,h in hh.items() if h in idx},missing_rust={n:h for n,h in hh.items() if h not in idx})
(E/'RECOVERED.json').write_text(json.dumps(rs,indent=2)+'\n');(E/'SOURCE_INDEX.json').write_text(json.dumps(idx,indent=2)+'\n')
print('receipts',len(rs),'matched',sum(len(x.get('matched_rust',{})) for x in rs),'missing',sum(len(x.get('missing_rust',{})) for x in rs))
