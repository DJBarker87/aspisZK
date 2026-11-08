"""Reuse only accepted exact-source objects with matching direct dependency hashes.
Run between batches, never concurrently with a compiler. This does not rebuild.
"""
import pathlib,json,lzma,hashlib,re,collections
R=pathlib.Path('/home/dombarker/project-offloads');V=R/'codex-pv-lib-slice-20261107/v1-coherence';O=V/'objects-resolved';E=V/'evidence';plan=json.load(open(V/'PLAN.json'))
sha=lambda p:hashlib.file_digest(open(p,'rb'),'sha256').hexdigest()
cs=json.load(open(V/'CACHE_SURVEY.json'));by=collections.defaultdict(list)
for c in cs:
 if c.get('source_sha256'):by[c['module']].append(c)
for base in [R/'codex-pv-lib-20261107',R/'codex-pv-lib-20261107/lane-A',R/'codex-pv-lib-slice-20261107',R/'codex-pv-lib-spec-20261107']:
 for f in list((base/'evidence').glob('receipt-*.json'))+list((base/'lane-B/evidence').glob('receipt-*.json')):
  r=json.load(open(f));m=r.get('target');h=r.get('object_sha256')
  if not r.get('accepted') or not h or m not in plan['rebuild']:continue
  source_hash=plan['rebuild'][m]['source_sha256']
  if r.get('source_sha256')!=source_hash:continue
  res=f.parent/f"resolution-{r['attempt']}.json.xz";res2=f.parent/f"resolution-{r['attempt']}.json"
  for d in base.glob('objects*'):
   o=d/(m+'.olean')
   if o.exists() and sha(o)==h:
    by[m].append(dict(module=m,path=str(o),sha256=h,source_sha256=source_hash,authority=str(res if res.exists() else res2) if res.exists() or res2.exists() else None,receipt=str(f),metrics={k:r.get(k) for k in ['exit','wall','peak_rss_kbytes','swaps','axioms_summary_based','source_revision']},dependency_hashes=r.get('dependency_hashes') or {k:v['sha256'] for k,v in r.get('dependencies',{}).items()}));break
cache={};hashed={};records=[]
def hashpath(p):
 if str(p) not in hashed:hashed[str(p)]=sha(p)
 return hashed[str(p)]
for m in plan['order']:
 o=O/(m+'.olean')
 if o.exists():continue
 deps=plan['rebuild'][m]['imports'];current={};missing=False
 for d in deps:
  if d=='Lean':continue
  q=O/(d.replace('.','/')+'.olean')
  if not q.exists():missing=True;break
  current[d]=hashpath(q)
 if missing:continue
 for c in by[m]:
  if c['source_sha256']!=plan['rebuild'][m]['source_sha256']:continue
  auth=c.get('authority');expected=c.get('dependency_hashes',{})
  if auth and pathlib.Path(auth).exists():
   if auth not in cache:
    p=pathlib.Path(auth);z=json.loads(lzma.decompress(p.read_bytes()) if p.suffix=='.xz' else p.read_bytes());cache[auth]=z.get('modules',z)
   expected={d:v['sha256'] for d,v in cache[auth].items() if isinstance(v,dict) and 'sha256' in v}
  if any(expected.get(d)!=h for d,h in current.items()):continue
  if hashpath(c['path'])!=c['sha256']:continue
  o.symlink_to(c['path'])
  for ext in ['.olean.private','.olean.server','.ilean','.ir']:
   src=pathlib.Path(str(c['path']).removesuffix('.olean')+ext);dest=pathlib.Path(str(o).removesuffix('.olean')+ext)
   if src.exists() and not dest.exists():dest.symlink_to(src)
  records.append(dict(module=m,merged_revision=plan['revision'],source_sha256=c['source_sha256'],object_sha256=c['sha256'],object_path=c['path'],authority=auth,original_receipt=c.get('receipt'),original_metrics=c.get('metrics'),dependency_hashes=current));break
p=E/'REUSE.json';old=json.load(open(p)) if p.exists() else [];p.write_text(json.dumps(old+records,indent=2))
left=[m for m in plan['order'] if not (O/(m+'.olean')).exists()]
print(json.dumps(dict(new_reuse=len(records),remaining=len(left),first=left[:8])))
