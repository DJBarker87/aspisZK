"""Import the sibling's committed symbolic zero proof, preserving ownership.
Only import-name fixes select the already coherent canonical RSL modules.
"""
from pathlib import Path
import subprocess,re,json,hashlib
E=Path(__file__).resolve().parent
rev=subprocess.check_output(['git','rev-parse','codex/cx-tx1-owned-20261107'],text=True).strip()
base='evidence/tx1-owned-20261111/'
paths=subprocess.check_output(['git','ls-tree','-r','--name-only',rev,base],text=True).splitlines()
source={}
for p in paths:
 if not p.endswith('.lean') or '/sources/' in p or '/raw/' in p or '/NMT_L' in p:continue
 rel=p.removeprefix(base)
 if '/' not in rel:source[rel[:-5]]=p
for p in paths:
 if '/NMT_lean/' in p and p.endswith('.lean'):source[p.split('/NMT_lean/')[1][:-5].replace('/','.')]=p
order=[];visited=set();records=[]
def collect(n):
 if n in visited:return
 visited.add(n)
 if n.startswith('RSL_'):
  p=E.parent/'rowspec-lead-20261107'/(n+'.lean');raw=p.read_bytes();origin='canonical RSL at HEAD';path=str(p)
 else:
  assert n.startswith('NMT_'),n
  path=source[n];raw=subprocess.check_output(['git','show',rev+':'+path]);origin=rev
 text=raw.decode()
 fixed=re.sub(r'(?m)^import NMT_RSL_(\w+)',r'import RSL_\1',text)
 assert not re.search(r'(?m)^\s*(axiom\s|.*:=\s*(sorry|admit)\b)',fixed),n
 for line in fixed.splitlines():
  if line.startswith('import '):
   for d in line[7:].split():
    if d.startswith(('NMT_','RSL_')):collect(d)
 dest=E/'NND_reuse'/'NND_zero_support'/(n.replace('.','/')+'.lean');dest.parent.mkdir(parents=True,exist_ok=True)
 if dest.exists():assert dest.read_text()==fixed
 else:dest.write_text(fixed)
 records.append(dict(module=n,revision=origin,path=path,sha256=hashlib.sha256(raw).hexdigest(),replay_sha256=hashlib.sha256(fixed.encode()).hexdigest(),changes=('canonical RSL import-name fixes only' if text!=fixed else 'none'),use='reuse committed zero lemma without duplicating proof'))
 order.append(dict(module=n,path=str(dest.relative_to(E))))
collect('NMT_345ZeroSource')
(E/'NND_ZERO_REUSE.json').write_text(json.dumps(dict(revision=rev,files=records,order=order),indent=1)+'\n')
print(json.dumps([r['module'] for r in order]))
