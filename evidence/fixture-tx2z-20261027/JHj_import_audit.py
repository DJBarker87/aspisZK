from pathlib import Path
import subprocess,re,json,hashlib
P=Path(__file__).resolve().parent;R=P.parents[1]
paths=[Path(x) for x in subprocess.check_output(['rg','--files','-g','*.lean'],cwd=R,text=True).splitlines()]
by={}
for p in paths:by.setdefault(p.stem,[]).append(p)
seen={};unresolved={};flags=[]
def select(n):
 for p in [Path('lean')/(n+'.lean'),Path('docs/research/100bit-spend-path-20261013/lean')/(n+'.lean'),Path('evidence/replay-deployed2-20261027')/(n+'.lean')]:
  if (R/p).exists():return p
 candidates=by.get(n.split('.')[-1],[])
 if len(candidates)==1:return candidates[0]
 if candidates:
  groups={hashlib.sha256((R/p).read_bytes()).hexdigest() for p in candidates}
  if len(groups)==1:return candidates[0]
 unresolved[n]=[str(p) for p in candidates];return None

def visit(n):
 if n in seen or n in unresolved:return
 if n.startswith(('XRn_','KSA_')):flags.append(n)
 p=select(n)
 if p is None:return
 seen[n]=str(p)
 for line in (R/p).read_text().splitlines():
  if line.startswith('import '):
   for child in line[7:].split():
    if child.startswith('--'):break
    visit(child)
for p in (R/'lean').glob('JHj_*.lean'):visit(p.stem)
(P/'JHj_IMPORT_AUDIT.json').write_text(json.dumps(dict(known_source_closure=seen,unresolved_source_origins=unresolved,forbidden_kit_prefixes_found=sorted(set(flags)),scope='Checkout source closure where exact module sources can be selected; unresolved entries are explicitly not a complete object-to-source attribution'),indent=2)+'\n')
assert not flags,flags
print(len(seen),'source modules inspected;',len(unresolved),'origins unresolved; no XRn_/KSA_ import in inspected closure')
