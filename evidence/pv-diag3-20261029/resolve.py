"""Resolve project sources in mandated precedence, never substitute a grep variant."""
from pathlib import Path
import subprocess,json,hashlib,re
E=Path(__file__).parent;rev=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip()
git=lambda p:subprocess.check_output(['git','show',p])
inv=json.loads(git('HEAD:evidence/envj-rebuild-20261026/EJR_final-inventory.json'))
ejr={r['module'].replace('/','.'):r for r in inv['selected'] if r.get('resolution') and r.get('workspace')=='joint'}
freeze=json.loads(git('HEAD:docs/research/100bit-spend-path-20261013/evidence/prover-commit47-20261022/final-source-freeze.json'))
fr={r['module']:r for r in freeze['sources']}
# Rebuild2 supplements EJR before the h5 fallback.
records=['evidence/envj-rebuild-20261026/EJR_all-restored-sources.json']+[f for f in subprocess.check_output(['git','ls-tree','-r','--name-only','HEAD','evidence/envj-rebuild2-20261026'],text=True).splitlines() if f.endswith('-payload.json') or f.endswith('/EJS_recursive-frontier.json')]
for f in records:
 d=json.loads(git('HEAD:'+f));rs=d if isinstance(d,list) else d.get('rows',[])
 for r in rs:
  name=r.get('module','').replace('/','.');a=r.get('resolution') or r
  if name and name not in ejr and a.get('path') and a.get('blob'):
   ejr[name]=dict(module=name,sha256=hashlib.sha256(git(a['blob'])).hexdigest(),resolution=a,addition=f)

ext={r['module'].replace('/','.') for r in json.loads((E/'external-authority.json').read_text())}
tracked=subprocess.check_output(['git','ls-tree','-r','--name-only','HEAD'],text=True).splitlines()
graph=json.loads(git('HEAD:docs/research/100bit-spend-path-20261013/evidence/import-union-20261022/host-module-graph.json'))
res={};gaps={};order=[]
def visit(m):
 if m in ext or m in res or m in gaps:return
 if m.startswith('XR'):raise Exception(m)
 if m in ejr:
  r=ejr[m];path=r['resolution']['path'];b=git(r['resolution']['blob']);kind='EJR';expected=r['sha256'];blob=r['resolution']['blob']
 elif m in fr:
  r=fr[m];path=r['path'];b=git(freeze['revision']+':'+path);kind='freeze';expected=r['sha256'];blob=subprocess.check_output(['git','rev-parse',freeze['revision']+':'+path],text=True).strip()
 else:
  tail=m.replace('.','/')+'.lean';ps=[p for p in tracked if p.endswith('/'+tail) or p==tail]
  # Explicit h5 paths inherited from candidate, generated cohort retained.
  explicit={
   'AspisR1CircleFallback.RawCircleFallbackOutputBridge':'evidence/pv-rw19-resume-20261026/retained-source-inputs/AspisR1CircleFallback.RawCircleFallbackOutputBridge.lean.txt',
   'R1Z.ProverRwFullFuns':'docs/research/100bit-spend-path-20261013/lean/prover-rw-20261023/ProverRwFullFuns.lean',
   'R1Z.ProverRwFullExternalTypes':'docs/research/100bit-spend-path-20261013/lean/prover-rw-20261023/ProverRwFullExternalTypes.lean',
   'R1Z.ProverRwFullExternalFuns':'docs/research/100bit-spend-path-20261013/lean/prover-rw-20261023/ProverRwFullExternalFuns.lean'}
  for name in ['RawCircleSampleActualPolicyUnconditionalV1','RawCircleSampleActualFallbackCoordinatesV1']:
   explicit['AspisR1CircleSampleWrapper.'+name]='docs/research/100bit-spend-path-20261013/lean-candidates/current-circle-wrapper-20261019/'+name+'.lean'
  if m in explicit:ps=[explicit[m]]
  if len(ps)!=1:
   gaps[m]=ps
   if m in graph:
    for dep in graph[m]['imports']:visit(dep)
   return
  path=ps[0];b=git('HEAD:'+path);kind='h5 HEAD';expected=hashlib.sha256(b).hexdigest();blob=subprocess.check_output(['git','rev-parse','HEAD:'+path],text=True).strip()
 assert hashlib.sha256(b).hexdigest()==expected,m
 clean=b.decode()
 while '/-' in clean:
  start=clean.index('/-');depth=1;i=start+2
  while depth and i<len(clean):
   if clean[i:i+2]=='/-':depth+=1;i+=2
   elif clean[i:i+2]=='-/':depth-=1;i+=2
   else:i+=1
  clean=clean[:start]+'\n'*clean[start:i].count('\n')+clean[i:]
 clean=re.sub(r'--[^\n]*','',clean)
 imports=re.findall(r'^(?:public )?import ([A-Za-z0-9_.]+)',clean,re.M)
 res[m]=dict(path=path,blob=blob,sha256=expected,authority=kind,imports=imports)
 canonical='docs/research/v8-r0-zk-20261009/lean/'+m.replace('.','/')+'.lean'
 if canonical in tracked and canonical!=path:
  alternate=git('HEAD:'+canonical);h=hashlib.sha256(alternate).hexdigest()
  if h!=expected:res[m]['tracked_conflict']=dict(path=canonical,sha256=h,selected_sha256=expected,ruling="h5-prime EJR/freeze wins")

 for i in imports:visit(i)
 order.append(m)

for root in ['R1Z.PV_RunJoin_Deployed','R1Z.PV_RunJoin_TrustItems','R1Z.ProverRwRetryModel']:visit(root)
(E/'project-resolution.json').write_text(json.dumps(dict(revision=rev,roots=['R1Z.ProverRwRetryModel'],modules=res,order=order,gaps=gaps),indent=2)+'\n')
print('resolved',len(res),'external',len(ext),'gaps',gaps)
# Only our private transport data, not new source authorities.
(E/'project-source-bytes.json').write_text(json.dumps({m:git(r['blob']).decode() for m,r in res.items()}))
