"""Freeze the final accepted own project closure at tracked HEAD; no object reuse."""
from pathlib import Path
import re,json,hashlib,subprocess
R=Path(__file__).resolve().parents[2];E=R/'evidence/pv-rdcd-20261028'
roots=['PV_RDCD_FinalManifest'];seen={}
def git(*args):return subprocess.check_output(['git',*args],cwd=R)
def go(m):
 if m in seen:return
 p=R/'docs/research/v8-r0-zk-20261009/lean'/(m.replace('.','/')+'.lean')
 if not p.exists():p=R/'docs/research/100bit-spend-path-20261013/lean/prover-rw-20261023'/(m.split('.')[-1]+'.lean')
 assert p.exists(),m
 b=p.read_bytes();rel=str(p.relative_to(R));assert b==git('show','HEAD:'+rel)
 deps=re.findall(r'^import\s+(\S+)',b.decode(),re.M)
 seen[m.replace('.','/')]=dict(path=rel,blob=git('rev-parse','HEAD:'+rel).decode().strip(),sha256=hashlib.sha256(b).hexdigest(),imports=[d.replace('.','/') for d in deps],authority='h5 tracked own source; initial EJR/freeze resolution census retained in git-pins/source-freeze-pins')
 for d in deps:
  if d.startswith('R1Z.'):go(d)
for root in roots:go('R1Z.'+root)
authorities={}
for ref in ['evidence/envj-rebuild-20261026/EJR_final-inventory.json','docs/research/100bit-spend-path-20261013/evidence/prover-commit47-20261022/final-source-freeze.json']:
 raw=git('show','research:'+ref);data=json.loads(raw);hits=[]
 def inspect(x):
  if isinstance(x,dict):
   for key in ['module','name']:
    if isinstance(x.get(key),str) and x[key].replace('.','/') in seen:hits.append(x)
   for v in x.values():inspect(v)
  elif isinstance(x,list):
   for v in x:inspect(v)
 inspect(data);assert not hits,(ref,hits)
 authorities[ref]=dict(research_blob=git('rev-parse','research:'+ref).decode().strip(),sha256=hashlib.sha256(raw).hexdigest(),matching_project_modules=hits)

(E/'resume-final-source-pins.json').write_text(json.dumps(dict(source_revision=git('rev-parse','HEAD').decode().strip(),modules=seen,authority_absence_checks=authorities,roots=['R1Z/'+r for r in roots]),indent=2)+'\n');print(len(seen),'tracked source closure pins')
