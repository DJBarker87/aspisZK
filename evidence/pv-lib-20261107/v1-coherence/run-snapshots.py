"""Run source-cohort and merged kernel-type snapshots, not another axioms audit.
Invoked inside one admitted capped scope; fresh process per original cohort.
"""
import pathlib,json,lzma,hashlib,subprocess,os,sys
V=pathlib.Path('/home/dombarker/project-offloads/codex-pv-lib-slice-20261107/v1-coherence');E=V/'evidence';O=V/'objects-canonical';base=json.load(open(V/'J.json'));a=int(sys.argv[1]);assert 56500<=a<=56589
sha=lambda p:hashlib.file_digest(open(p,'rb'),'sha256').hexdigest()
# Split the 95 MiB source-authority manifest in a short-lived preparation process.
# Keep only one original cohort's authority in the parent beside a Lean child.
prep="""import pathlib,json,lzma,sys
V=pathlib.Path(sys.argv[1]);D=V/'snapshot-plans';D.mkdir(exist_ok=True)
groups=json.loads(lzma.decompress((V/'SNAPSHOT_PLAN.json.xz').read_bytes()));names=[]
for g in groups:
 p=D/(g['driver']+'.json.xz');p.write_bytes(lzma.compress(json.dumps(g).encode()));names.append(str(p))
(D/'index.json').write_text(json.dumps(names))
"""
subprocess.run([sys.executable,'-c',prep,str(V)],check=True)
group_paths=json.load(open(V/'snapshot-plans/index.json'))
def snapshot(name,request,path):
 env=os.environ.copy()
 for k,v in base.items():
  if v is None:env.pop(k,None)
  else:env[k]=v
 env['LEAN_PATH']=str(path)
 log=E/f'statements-{a}-{name}.jsonl';tim=E/f'statements-{a}-{name}.time'
 cmd=['/usr/bin/time','-v','-o',str(tim),'timeout','600',base['LEAN'],'-j1','-M7000','-DElab.async=false','--run',str(V/'sources-canonical/PV_LIB_V1_StatementSnapshot.lean'),str(request)]
 with log.open('w') as f:r=subprocess.run(cmd,env=env,stdout=f,stderr=subprocess.STDOUT,cwd=V)
 if r.returncode:
  print(name,'FAILED',log.read_text()[-4000:],flush=True);sys.exit(1)
 return dict(exit=r.returncode,sha256=sha(log),log=str(log),time=str(tim),command=cmd,types={x['root']:{k:v for k,v in x.items() if k!='root'} for x in (json.loads(l) for l in log.read_text().splitlines() if l.startswith('{'))})
# Reuse completed, hash-checked merged results from 56560; only the baseline
# framework overlay changed. No unchanged merged scan or completed comparison rerun.
union=json.load(open(V/'AUDIT_ROOTS.json'));merged_types={}
merged_parts=json.load(open(E/'MERGED_TYPE_BATCHES-56560.json'))
for part in merged_parts:
 assert part['exit']==0 and sha(part['log'])==part['sha256']
 for line in pathlib.Path(part['log']).read_text().splitlines():
  if line.startswith('{'):
   q=json.loads(line);assert q['root'] not in merged_types;merged_types[q['root']]={k:v for k,v in q.items() if k!='root'}
assert set(merged_types)==set(union['roots'])
merged=dict(exit=0,types=merged_types,parts=merged_parts,one_frozen_object_mapping=True,reused_attempt=56560)
print('Reused exact merged-cohort types:',len(merged_types),flush=True)
(E/f'MERGED_TYPE_BATCHES-{a}.json').write_text(json.dumps(merged_parts,indent=2))
results=json.load(open(E/'STATEMENT_COMPARISONS-56561.json'));completed={r['group'] for r in results}
# A fallback PV dependency is admissible only when all retained verified
# authorities agree on its exact historical object hash. Cohort entries win.
survey=json.load(open(V/'CACHE_SURVEY.json'));candidates={}
for c in survey:
 if c['module'].startswith('PV_'):candidates.setdefault(c['module'],[]).append(c)
shared_unique={m:vs[0] for m,vs in candidates.items() if len({v['sha256'] for v in vs})==1}
framework=[]
for q in O.rglob('*.olean'):
 rel=q.relative_to(O)
 if not rel.parts[0].startswith('PV_'):framework.append((rel,q))
for group_path in group_paths:
 g=json.loads(lzma.decompress(pathlib.Path(group_path).read_bytes()))
 name=g['driver']
 if name in completed:continue
 dest=V/'snapshot-authorities'/name;dest.mkdir(parents=True,exist_ok=True)
 if 'host_resolution' in g:
  p=pathlib.Path(g['host_resolution']);z=json.loads(lzma.decompress(p.read_bytes()));authority=z.get('modules',z)
 else:authority=g['resolution']
 (E/('BASELINE_AUTHORITY-'+name+'.json.xz')).write_bytes(lzma.compress(json.dumps(authority).encode()))
 for m,v in authority.items():
  if not isinstance(v,dict) or 'path' not in v:continue
  p=pathlib.Path(v['path']);assert sha(p)==v['sha256'],('baseline cache changed',name,m)
  q=dest/(m.replace('.','/')+'.olean');q.parent.mkdir(parents=True,exist_ok=True)
  if not q.exists():q.symlink_to(p)
  for ext in ['.olean.private','.olean.server','.ilean','.ir']:
   src=pathlib.Path(str(p).removesuffix('.olean')+ext);link=pathlib.Path(str(q).removesuffix('.olean')+ext)
   if src.exists() and not link.exists():link.symlink_to(src)
 # Early compiler resolutions omitted the base environment's transitive
 # entries. Complete them from that cohort's retained named hash authority.
 shared_kind={'PV_LIB_SPEC_RawAuditBase':'BASE','PV_LIB_SPEC_RawAuditStx':'STX','PV_LIB_SPEC_RawAuditSession2':'BASE','PV_LIB_SPEC_RawAuditSession19':'ACTIVE19'}.get(name)
 shared_used={}
 if shared_kind:
  source_authority=V.parents[0]/'codex-pv-lib-spec-20261107'/(shared_kind+'_OBJECT_AUTHORITY.json.xz')
  # V.parent is the slice job, V.parents[1] is project-offloads.
  source_authority=V.parents[1]/'codex-pv-lib-spec-20261107'/(shared_kind+'_OBJECT_AUTHORITY.json.xz')
  shared=json.loads(lzma.decompress(source_authority.read_bytes()))['modules']
  for m,v in shared.items():
   q=dest/(m.replace('.','/')+'.olean')
   if q.exists():continue
   src=pathlib.Path(v['path']);assert sha(src)==v['sha256'],('source baseline authority changed',name,m)
   q.parent.mkdir(parents=True,exist_ok=True);q.symlink_to(src);shared_used[m]=v
   for ext in ['.olean.private','.olean.server','.ilean','.ir']:
    part=pathlib.Path(str(src).removesuffix('.olean')+ext);link=pathlib.Path(str(q).removesuffix('.olean')+ext)
    if part.exists() and not link.exists():link.symlink_to(part)
  (E/('BASELINE_SHARED_AUTHORITY-'+name+'.json.xz')).write_bytes(lzma.compress(json.dumps(shared_used).encode()))
 unique_used={}
 for m,v in shared_unique.items():
  q=dest/(m.replace('.','/')+'.olean')
  if q.exists():continue
  src=pathlib.Path(v['path']);assert sha(src)==v['sha256'],('shared historical cache changed',m)
  q.parent.mkdir(parents=True,exist_ok=True);q.symlink_to(src);unique_used[m]=v
  for ext in ['.olean.private','.olean.server','.ilean','.ir']:
   part=pathlib.Path(str(src).removesuffix('.olean')+ext);link=pathlib.Path(str(q).removesuffix('.olean')+ext)
   if part.exists() and not link.exists():link.symlink_to(part)
 (E/('BASELINE_UNIQUE_SHARED-'+name+'.json.xz')).write_bytes(lzma.compress(json.dumps(unique_used).encode()))
 # Complete the standard/toolchain framework from the SAME hash-frozen cache.
 # No PV proof module is supplied by this fallback, and authority entries win.
 fallback={}
 for rel,src in framework:
  q=dest/rel
  if q.exists():continue
  q.parent.mkdir(parents=True,exist_ok=True);q.symlink_to(src)
  fallback[str(rel)]=dict(path=str(src),sha256=sha(src))
  for ext in ['.olean.private','.olean.server','.ilean','.ir']:
   part=pathlib.Path(str(src).removesuffix('.olean')+ext);link=pathlib.Path(str(q).removesuffix('.olean')+ext)
   if part.exists() and not link.exists():link.symlink_to(part)
 (E/('BASELINE_FRAMEWORK-'+name+'.json.xz')).write_bytes(lzma.compress(json.dumps(fallback).encode()))
 # Only requested roots are compared; historical drivers also contain eight extra roots.
 roots=[r for r in g['roots'] if r in merged['types']]
 request=V/(name+'-snapshot.json');request.write_text(json.dumps(dict(modules=g['modules'],roots=roots)))
 source=snapshot(name+'-source',request,dest)
 differences=[root for root in roots if source['types'][root]!=merged['types'][root]]
 rec=dict(group=name,roots=len(roots),differences=differences,source_cohort_attempt=g['attempt'],source={k:v for k,v in source.items() if k!='types'},merged={k:v for k,v in merged.items() if k!='types'})
 results.append(rec);(E/f'STATEMENT_COMPARISONS-{a}.json').write_text(json.dumps(results,indent=2));print(json.dumps(dict(group=name,roots=len(roots),differences=len(differences))),flush=True)
 if differences:print(differences,flush=True)
sys.exit(1 if any(r['differences'] for r in results) else 0)
