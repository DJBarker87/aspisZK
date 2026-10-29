from pathlib import Path
import json,re,os
D=Path('/home/dombarker/project-offloads/codex-pv-mfe-20261029');B=D.parent;pattern=re.compile(r'(?<![A-Za-z0-9])(703\d\d)(?![A-Za-z0-9])');hits=[];sent=[];examined=0
for job in B.iterdir():
 if not job.is_dir() or job==D:continue
 roots=[job/'evidence',job/'receipts',job/'tools',job]
 # Shared launchers and private line directories both retain sent ledgers.
 for root in roots:
  for p in root.glob('sent*.txt'):
   try:ls=p.read_text(errors='replace').splitlines()
   except OSError:continue
   sent.append(str(p))
   for line in ls:
    parts=line.split()
    if len(parts)>2 and parts[2].isdigit() and 70300<=int(parts[2])<=70399:hits.append(dict(path=str(p),line=line))
 for root in [job/'evidence',job/'receipts']:
  if not root.is_dir():continue
  for cur,dirs,files in os.walk(root):
   dirs[:]=[x for x in dirs if x not in ['target','.git','objects','lean-objects','sources','lean-sources','node_modules']]
   for name in dirs+files:
    examined+=1
    if pattern.search(name):hits.append(dict(path=str(Path(cur)/name)))
 for p in job.glob('lean-703*'):
  if pattern.search(p.name):hits.append(dict(path=str(p)))
# The unified launcher ledger can sit below its integration root.
for p in (B/'r1-privacy-build-integration-20261019').glob('**/sent*.txt'):
 if str(p) in sent:continue
 sent.append(str(p))
 for line in p.read_text(errors='replace').splitlines():
  parts=line.split()
  if len(parts)>2 and parts[2].isdigit() and 70300<=int(parts[2])<=70399:hits.append(dict(path=str(p),line=line))
j=dict(range=[70300,70399],sent_ledgers=sorted(set(sent)),receipt_names_examined=examined,foreign_matches=hits,initial_prelaunch_scan='Immediate per-job lean-703xx receipt directories only; no collisions. The sent/nested audit was completed retrospectively.',rerun_for_id_audit=False);(D/'id-retrospective-audit.json').write_text(json.dumps(j,indent=2)+'\n');print('sent ledgers',len(set(sent)),'receipt names',examined,'foreign matches',len(hits))
