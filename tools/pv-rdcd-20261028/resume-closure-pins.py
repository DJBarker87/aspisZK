"""Freeze the final accepted own project closure at tracked HEAD; no object reuse."""
from pathlib import Path
import re,json,hashlib,subprocess
R=Path(__file__).resolve().parents[2];E=R/'evidence/pv-rdcd-20261028'
roots=['PV_RDCD_FinalReplay'];seen={}
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
(E/'resume-final-source-pins.json').write_text(json.dumps(dict(source_revision=git('rev-parse','HEAD').decode().strip(),modules=seen,roots=['R1Z/'+r for r in roots]),indent=2)+'\n');print(len(seen),'tracked source closure pins')
