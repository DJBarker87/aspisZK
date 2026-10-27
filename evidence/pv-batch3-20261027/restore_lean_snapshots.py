"""Recover early draft snapshots by exact SHA; never infer a matching source."""
from pathlib import Path
import json,hashlib
D=Path(__file__).resolve().parent;L=D/'lean';variants=[]
for p in L.glob('*.lean'):variants.append((str(p),p.read_text()))
t=(L/'PV_B3_Forest_134_Types.lean').read_text();with_disc=t.replace('@[rust_type','@[discriminant isize, rust_type');variants += [('types-discriminant',with_disc),('types-singular',with_disc.replace('RustAttributes','RustAttr')),('types-umbrella',with_disc.replace('import Aeneas.Std\nimport Aeneas.Tactic.RustAttributes\n','import Aeneas\n'))]
t=(L/'PV_B3_MaskLoopDone.lean').read_text();with_rfl=t.replace('  rw [PV_B3_MaskLoopStop.body_done producers consumers masks i h]\n','  rw [PV_B3_MaskLoopStop.body_done producers consumers masks i h]\n  rfl\n');variants += [('loopdone-dsimp-rfl',with_rfl),('loopdone-rfl',with_rfl.replace('  dsimp only\n',''))]
t=(L/'PV_B3_MaskCounter.lean').read_text();variants.append(('counter-before-tuple-reduction',t.replace('        dsimp only\n','')))
records=[]
for p in sorted((D/'receipts').glob('lean-*/submission.json')):
 sub=json.loads(p.read_text());wanted=sub['source_sha256'];match=next(((n,s)for n,s in variants if hashlib.sha256(s.encode()).hexdigest()==wanted),None)
 out=p.parent/'source.lean'
 if match and not out.exists():out.write_text(match[1])
 found=out.exists() and hashlib.sha256(out.read_bytes()).hexdigest()==wanted
 records.append(dict(attempt=sub['attempt'],module=sub['module'],sha256=wanted,recovered=found,variant=match[0]if match else None))
(D/'lean-snapshot-recovery.json').write_text(json.dumps(records,indent=2)+'\n');print(json.dumps(dict(total=len(records),recovered=sum(r['recovered']for r in records),missing=[r['attempt']for r in records if not r['recovered']]),indent=2))
