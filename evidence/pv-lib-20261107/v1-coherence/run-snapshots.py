"""Run source-cohort and merged kernel-type snapshots, not another axioms audit.
Invoked inside one admitted capped scope; fresh process per original cohort.
"""
import pathlib,json,lzma,hashlib,subprocess,os,sys
V=pathlib.Path('/home/dombarker/project-offloads/codex-pv-lib-slice-20261107/v1-coherence');E=V/'evidence';O=V/'objects-resolved';groups=json.loads(lzma.decompress((V/'SNAPSHOT_PLAN.json.xz').read_bytes()));base=json.load(open(V/'J.json'));a=int(sys.argv[1]);assert 56500<=a<=56589
sha=lambda p:hashlib.file_digest(open(p,'rb'),'sha256').hexdigest()
results=[];authorities={}
for g in groups:
 name=g['driver'];dest=V/'snapshot-authorities'/name;dest.mkdir(parents=True,exist_ok=True)
 if 'host_resolution' in g:
  p=pathlib.Path(g['host_resolution']);z=json.loads(lzma.decompress(p.read_bytes()));authority=z.get('modules',z)
 else:authority=g['resolution']
 authorities[name]=authority
 (E/'BASELINE_AUTHORITIES.json.xz').write_bytes(lzma.compress(json.dumps(authorities).encode()))
 for m,v in authority.items():
  if not isinstance(v,dict) or 'path' not in v:continue
  p=pathlib.Path(v['path']);assert sha(p)==v['sha256'],('baseline cache changed',name,m)
  q=dest/(m.replace('.','/')+'.olean');q.parent.mkdir(parents=True,exist_ok=True)
  if not q.exists():q.symlink_to(p)
  for ext in ['.olean.private','.olean.server','.ilean','.ir']:
   src=pathlib.Path(str(p).removesuffix('.olean')+ext);link=pathlib.Path(str(q).removesuffix('.olean')+ext)
   if src.exists() and not link.exists():link.symlink_to(src)
 request=V/(name+'-snapshot.json');request.write_text(json.dumps({k:g[k] for k in ['modules','roots']}))
 outputs={}
 for mode,path in [('source',dest),('merged',O)]:
  env=os.environ.copy()
  for k,v in base.items():
   if v is None:env.pop(k,None)
   else:env[k]=v
  env['LEAN_PATH']=str(path)
  log=E/f'statements-{a}-{name}-{mode}.jsonl';tim=E/f'statements-{a}-{name}-{mode}.time'
  cmd=['/usr/bin/time','-v','-o',str(tim),'timeout','600',base['LEAN'],'-j1','-M7000','-DElab.async=false','--run',str(V/'sources/PV_LIB_V1_StatementSnapshot.lean'),str(request)]
  with log.open('w') as f:r=subprocess.run(cmd,env=env,stdout=f,stderr=subprocess.STDOUT,cwd=V)
  outputs[mode]=dict(exit=r.returncode,sha256=sha(log),log=str(log),time=str(tim),command=cmd)
  if r.returncode:
   print(name,mode,'FAILED',log.read_text()[-4000:],flush=True);sys.exit(1)
  outputs[mode]['types']={x['root']:{k:v for k,v in x.items() if k!='root'} for x in map(json.loads,log.read_text().splitlines())}
 differences=[root for root in g['roots'] if outputs['source']['types'][root]!=outputs['merged']['types'][root]]
 rec=dict(group=name,roots=len(g['roots']),differences=differences,source_cohort_attempt=g['attempt'],source={k:v for k,v in outputs['source'].items() if k!='types'},merged={k:v for k,v in outputs['merged'].items() if k!='types'})
 results.append(rec);(E/f'STATEMENT_COMPARISONS-{a}.json').write_text(json.dumps(results,indent=2));print(json.dumps(dict(group=name,roots=len(g['roots']),differences=len(differences))),flush=True)
 if differences:print(differences,flush=True)
sys.exit(1 if any(r['differences'] for r in results) else 0)
