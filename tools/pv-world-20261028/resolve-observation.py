"""Resolve the existing trust Observation's project closure, in authority order.
Read-only planning; never substitutes a similarly named source or shared object.
"""
from pathlib import Path
import subprocess,json,hashlib,re
R=Path(__file__).resolve().parents[2];E=R/'evidence/pv-world-20261028'
git=lambda *a:subprocess.check_output(['git',*a],cwd=R)
sha=lambda b:hashlib.sha256(b).hexdigest()
rev=git('rev-parse','HEAD').decode().strip()
ej=json.loads((R/'evidence/envj-rebuild-20261026/EJR_final-inventory.json').read_bytes())
pins={x['module'].replace('/','.'):x for x in ej['selected'] if x.get('resolution')}
f=json.loads((R/'docs/research/100bit-spend-path-20261013/evidence/prover-commit47-20261022/final-source-freeze.json').read_bytes())
frozen={x['module'].replace('/','.'):x for x in f['sources']}
external={x['module'].replace('/','.') for x in json.loads((E/'external-object-manifest.json').read_bytes())}
tracked={}
for p in git('ls-files','*.lean').decode().splitlines():
 if '/lean/' in p:tracked.setdefault(p.split('/lean/',1)[1][:-5].replace('/','.'),[]).append(p)
# The frozen extraction module associations are recorded in this job's h5 audit.
for x in json.loads((E/'extraction-dependencies.json').read_text()):tracked[x['module']]=[x['path']]
for m,x in json.loads((R/'evidence/pv-cbmid-20261027/LEAN-IMPORT-PROVENANCE.json').read_text()).items():tracked['R1Z.'+m]=[x['local_source']]
rows={};order=[];errors=[]
def visit(m):
 if m in rows or m in external:return
 if m.startswith('XR') or '.XR' in m:raise RuntimeError(('forbidden',m))
 if m in pins:
  x=pins[m];q=x['resolution'];b=git('cat-file','blob',q['blob']);assert sha(b)==x['sha256'];a='EJR';r=q['revision'];p=q['path'];blob=q['blob']
 elif m in frozen:
  x=frozen[m];r=f['revision'];p=x['path'];b=git('show',r+':'+p);assert sha(b)==x['sha256'];a='freeze';blob=git('rev-parse',r+':'+p).decode().strip()
 else:
  ps=tracked.get(m,[])
  if len(ps)!=1:errors.append(dict(module=m,issue='unresolved h5 association',paths=ps));rows[m]={};return
  p=ps[0];r=rev;b=git('show','HEAD:'+p);assert b==(R/p).read_bytes();a='h5';blob=git('rev-parse','HEAD:'+p).decode().strip()
 deps=re.findall(r'^import\s+(\S+)',b.decode(),re.M)
 rows[m]=dict(authority=a,revision=r,path=p,blob=blob,sha256=sha(b),imports=deps,tracked_alternatives=[dict(path=p,sha256=sha(git('show','HEAD:'+p))) for p in tracked.get(m,[])])
 for d in deps:visit(d)
 order.append(m)
visit('R1Z.PV_RunJoin_TrustItems')
j=dict(root='R1Z.PV_RunJoin_TrustItems',source_revision=rev,modules=rows,order=order,errors=errors)
(E/'observation-resolution.json').write_text(json.dumps(j,indent=2)+'\n')
print(json.dumps(dict(project=len(rows),h5=sum(x.get('authority')=='h5' for x in rows.values()),errors=errors)))
