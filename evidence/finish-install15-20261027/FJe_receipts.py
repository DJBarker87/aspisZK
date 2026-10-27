"""Read retained receipts only;no compiler or proof rerun."""
from pathlib import Path
import json,hashlib,re
P=Path(__file__).resolve().parent;R=P.parents[1]
rows=[];passed={}
for d in sorted(P.iterdir()):
 if not d.is_dir() or not re.fullmatch(r'FJe_(?:K)?\d{3}',d.name):continue
 f=d/'receipt.json'
 if not f.exists():continue
 x=json.loads(f.read_text())
 row={k:x.get(k) for k in ['attempt','kind','command','exit_status','wall_seconds','peak_rss_kib','swaps','cgroup_memory_peak_bytes','source_revision','source_hashes','print_axioms']}
 rows.append(row)
 if x['kind']=='lean' and x['exit_status']==0:
  for name,digest in x['source_hashes'].items():passed.setdefault(name,[]).append((digest,d.name))
mods=[]
for f in sorted((R/'lean').glob('FJe_*.lean')):
 digest=hashlib.sha256(f.read_bytes()).hexdigest();receipts=[n for h,n in passed.get(f.name,[]) if h==digest]
 mods.append(dict(source=str(f.relative_to(R)),sha256=digest,passing_receipts=receipts))
text=dict(lean_used=sum(r['kind']=='lean' for r in rows),kani_used=sum(r['kind']=='kani' for r in rows),attempts=rows,current_modules=mods,unverified_current=[x['source'] for x in mods if not x['passing_receipts']])
(P/'FJe_receipts.json').write_text(json.dumps(text,indent=2)+'\n')
print(json.dumps({k:text[k] for k in ['lean_used','kani_used','unverified_current']},indent=2))
