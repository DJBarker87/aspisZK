#!/usr/bin/env python3
"""Copy committed sibling evidence only; no merge or live-worktree access."""
from pathlib import Path
import hashlib,json,subprocess
E=Path(__file__).resolve().parent;R=E.parent.parent
REV='1e42726180';P='evidence/slice-q-leaves-20261029/'
full=subprocess.check_output(['git','rev-parse',REV],cwd=R,text=True).strip()
paths=subprocess.check_output(['git','ls-tree','-r','--name-only',full,P],cwd=R,text=True).splitlines();records=[]
for p in paths:
 raw=subprocess.check_output(['git','show',full+':'+p],cwd=R)
 assert len(raw)<=20*1024**2
 q=E/'NEB_IMPORTED_POINT'/p.removeprefix(P);q.parent.mkdir(parents=True,exist_ok=True);q.write_bytes(raw)
 records.append(dict(source_revision=full,source_path=p,path=str(q.relative_to(R)),sha256=hashlib.sha256(raw).hexdigest(),bytes=len(raw)))
(E/'NEB_POINT_IMPORTS.json').write_text(json.dumps(dict(branch='codex/cx-slice-q-leaves-20261029',revision=full,policy='Committed sources copied byte-for-byte; proofs imported rather than rewritten; no local bridge promoted to composition',files=records),indent=1)+'\n')
print(json.dumps(dict(revision=full,files=len(records))))
