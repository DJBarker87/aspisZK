"""Read retained hash authorities without loading Lean or modifying caches."""
import pathlib,json,lzma,hashlib
R=pathlib.Path('/home/dombarker/project-offloads');P=R/'codex-pv-lib-slice-20261107';E=P/'v1-coherence';E.mkdir(exist_ok=True)
checks={}; origins={}
for base in [R/'codex-pv-lib-spec-20261107',R/'codex-pv-lib-20261107/lane-A',P,R/'codex-pv-lib-20261107',R/'codex-pv-int-20261106']:
 for p in list(base.glob('*AUTHORITY*.json.xz'))+list((base/'evidence').glob('resolution-*.json.xz')):
  try:
   x=json.loads(lzma.decompress(p.read_bytes()));x=x.get('modules',x)
   if not isinstance(x,dict):continue
   for m,v in x.items():
    if isinstance(v,dict) and 'path' in v and 'sha256' in v:
     key=(m,v['path'],v['sha256']);checks[key]=v;origins[key]=str(p)
  except Exception:pass
result=[]
for (m,p,h),v in checks.items():
 q=pathlib.Path(p)
 if not q.exists():continue
 # Authority hash must match before it is a candidate.
 if hashlib.file_digest(q.open('rb'),'sha256').hexdigest()!=h:continue
 s=pathlib.Path(str(q).replace('/objects','/sources').removesuffix('.olean')+'.lean')
 # Most cohort object directories share /sources.
 if not s.exists():
  for a in q.parents:
   if a.name.startswith('objects'):
    s=a.parent/'sources'/q.relative_to(a).with_suffix('.lean');break
 result.append(dict(module=m,**v,authority=origins[(m,p,h)],source=str(s) if s.exists() else None,source_sha256=hashlib.file_digest(s.open('rb'),'sha256').hexdigest() if s.exists() else None))
(E/'CACHE_SURVEY.json').write_text(json.dumps(result));print('verified candidates',len(result),'modules',len(set(x['module'] for x in result)))
