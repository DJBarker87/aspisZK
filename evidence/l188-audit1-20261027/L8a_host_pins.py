"""Read-only cohort/tool availability pins; no compilation or extraction."""
from pathlib import Path
import hashlib,json,sys
B=Path('/home/dombarker/project-offloads/codex-cx-replay-dry-20261026')
T=Path('/home/dombarker/.elan/toolchains/leanprover--lean4---v4.32.0')
roots=[T/'lib/lean',B/'RPz8_overlay',B/'RPz7_overlay',B/'RPz4_trusted',B/'RPz_trusted']
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
rows=[]
for name in ['RPz8_Rc10_Top','RPz8_ARX_Root','AspisR1PublicPreparation.Types','AspisR1PublicPreparation.Funs','Aeneas.Std.Core.Fmt']:
 candidates=[r/(name.replace('.','/')+'.olean') for r in roots]
 p=next(p for p in candidates if p.is_file())
 rows.append(dict(module=name,selected=str(p),resolved=str(p.resolve()),sha256=sha(p),bytes=p.stat().st_size))
paths=[Path('/home/dombarker/project-offloads/v7-tag73-challenge-qm31-source-20260825-work/toolchain/output/aeneas-b59d5188-lean432-extended-static'),Path('/home/dombarker/project-offloads/aspis-r1-worker-c-tx1-accumulator-20261016/VerifyPreparedPrefix.llbc')]
print(json.dumps(dict(ordered_roots=list(map(str,roots)),selected=rows,historical_extraction_inputs=[dict(path=str(p),exists=p.is_file(),sha256=sha(p) if p.is_file() else None) for p in paths]),indent=2))
