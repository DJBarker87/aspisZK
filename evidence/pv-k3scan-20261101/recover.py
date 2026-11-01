import subprocess,pathlib,json,re,lzma,hashlib,collections
E=pathlib.Path(__file__).resolve().parent
rs=json.loads((E/'RECEIPTS.json').read_text());sp=json.loads((E/'SOURCE_PATHS.json').read_text());blob=E/'blobs';idx=collections.defaultdict(list);manifest={};seen=set()
def get(rev,p):
 r=subprocess.run(['git','show',rev+':'+p],capture_output=True);return r.stdout if r.returncode==0 else None
def put(b,rev,p):
 h=hashlib.sha256(b).hexdigest();idx[h].append({'revision':rev,'path':p});q=blob/(h+'.rs');
 if not q.exists():q.write_bytes(b)
 return h
# Exact tool sources and archived harness snapshots. Avoid compiler execution.
for ref,tree in sp.items():
 rev=tree['revision'];ns=tree['files'];dirs=set(x['path'].split('/')[1] for x in rs if x['branch']==ref)
 candidates=[p for p in ns if p.endswith(('.rs','.rs.txt')) and (p.split('/')[1] in dirs or '/v244/' in p)]
 # add retained evidence snapshots for the Kani families represented on this ref
 allnames=subprocess.check_output(['git','ls-tree','-r','--name-only',rev,'evidence/']).decode().splitlines()
 candidates += [p for p in allnames if p.endswith(('.rs','.rs.txt')) and p.split('/')[1] in dirs]
 for p in candidates:
  if p in seen:continue
  seen.add(p);b=get(rev,p)
  if b is not None:put(b,rev,p)
 print(ref,len(idx),'distinct source blobs',flush=True)
# Try exact recorded source path at receipt source revision and containing branch.
for x in rs:
 r=x['receipt']
 if not isinstance(r,dict):continue
 hashes={}
 for fld in ['inputs','source_hashes','source_sha256','sources']:
  a=r.get(fld,{})
  if isinstance(a,dict):
   for n,v in a.items():
    h=v.get('sha256') if isinstance(v,dict) else v
    if isinstance(h,str) and len(h)==64 and n.endswith(('.rs','.rs.txt')):hashes[n]=h
 hscalar=r.get('source_sha256')
 if isinstance(hscalar,str) and len(hscalar)==64:hashes['receipt-pinned-source.rs']=hscalar
 for n,h in hashes.items():
  if h in idx:continue
  m=re.search(r'(?:^|/)((?:tools|crates|programs)/.*\.rs)$',n);path=m[1] if m else n
  for rev in [r.get('source_revision'),r.get('revision'),x['revision']]:
   if not rev:continue
   b=get(str(rev),path)
   if b is not None and hashlib.sha256(b).hexdigest()==h:put(b,rev,path);break
 x['recorded_rust_hashes']=hashes
 x['matched_rust']={n:{'sha256':h,'provenance':idx[h][0]} for n,h in hashes.items() if h in idx}
 x['missing_rust']={n:h for n,h in hashes.items() if h not in idx}
(E/'RECOVERED.json').write_text(json.dumps(rs,indent=2)+'\n')
(E/'SOURCE_INDEX.json').write_text(json.dumps(idx,indent=2)+'\n')
print('matched',sum(len(x.get('matched_rust',{})) for x in rs),'missing',sum(len(x.get('missing_rust',{})) for x in rs))
