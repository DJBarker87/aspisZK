"""Collect textual targeted MIR; retain all-pass inventory by hash/size if >5MB."""
from pathlib import Path
import hashlib,json,shutil,re
D=Path(__file__).resolve().parent;O=D/'packet';M=D/'mir';T=O/'mir';T.mkdir(exist_ok=False)
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
rows=[];selected=[]
passes=['built.after.mir','nll.0.mir','ElaborateDrops.before.mir','ElaborateDrops.after.mir','runtime-optimized.after.mir','AddMovesForPackedDrops.before.mir']
for p in sorted(M.iterdir()):
 if not p.is_file():continue
 rows.append(dict(name=p.name,size=p.stat().st_size,sha256=sha(p)))
 n=p.name
 wanted=(n.startswith('prover_rw_resume_scalar.') and any(t in n for t in ['-draw.','-resume.','-run.','-from.','-entropy_nonzero32.'])) or (n.startswith('zeroize.') and any(t in n for t in ['-drop.','-prover_rw_resume_scalar_observe.','-prover_rw_resume_scalar_byte.','-record.','-coordinate.','-initialize.'])) or (n.startswith('core.ptr-drop_in_place.') and any(t in n for t in ['Instrumented','Original','Zeroizing_[u8;32]','Zeroizing_[u8;64]']))
 if wanted and any(n.endswith(t) for t in passes):
  shutil.copy2(p,T/n);selected.append(rows[-1])
full=O/'all-dump-inventory.remote.json';full.write_text(json.dumps(rows,separators=(',',':'))+'\n')
summary=dict(schema='ProverRwResumeMIR-collection-v1',all_dump_inventory=dict(path=str(full),size=full.stat().st_size,sha256=sha(full),files=len(rows),dump_bytes=sum(r['size'] for r in rows)),selected=selected)
(O/'collection.json').write_text(json.dumps(summary,indent=2)+'\n')
# No object copied. Inventory only for binaries/other generated artifacts.
artifacts=[dict(path=str(p.relative_to(D)),size=p.stat().st_size,sha256=sha(p)) for p in sorted((D/'target').rglob('*')) if p.is_file()]
(O/'generated-artifacts.json').write_text(json.dumps(artifacts,indent=2)+'\n')
print(json.dumps(dict(selected=len(selected),bytes=sum(r['size'] for r in selected),all_inventory=summary['all_dump_inventory'])))
