"""Pin final local handoff files; proof source hashes stay in their run receipts."""
from pathlib import Path
import json,hashlib,subprocess
E=Path(__file__).resolve().parent;R=E.parent.parent
records=[]
for relative in subprocess.check_output(['git','ls-files','--',str(E.relative_to(R))],cwd=R,text=True).splitlines():
 p=R/relative
 if not p.is_file() or p.name=='NFM_HANDOFF_MANIFEST.json':continue
 if '__pycache__' in p.parts:raise AssertionError(p)
 b=p.read_bytes();assert len(b)<20_000_000,p
 d=dict(path=str(p.relative_to(R)),bytes=len(b),sha256=hashlib.sha256(b).hexdigest())
 if p.is_symlink():d['symlink']=str(p.readlink())
 records.append(d)
out=dict(schema='NFM-final-files-v1',certificate_audit_commit='6e6c1620f16',source_revision=subprocess.check_output(['git','rev-parse','6e6c1620f16'],cwd=R,text=True).strip(),files=records,no_shipped_changes=True,no_push=True)
(E/'NFM_HANDOFF_MANIFEST.json').write_text(json.dumps(out,indent=1)+'\n')
print('pinned',len(records),'files')
