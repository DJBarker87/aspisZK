#!/usr/bin/env python3
"""Export small reviewable proof receipts, retaining hashes of long logs."""
import hashlib,json,re,shutil
from pathlib import Path
BASE=Path('/home/dombarker/project-offloads/codex-cx-r22-overflow-20261021')
export=BASE/'export';export.mkdir(exist_ok=True)
rows=[]
for d in sorted((BASE/'receipts').iterdir()):
    if not (d/'receipt.json').exists():continue
    dest=export/d.name;dest.mkdir(exist_ok=True)
    rec=json.loads((d/'receipt.json').read_text());raw=(d/'stdout.log').read_bytes();s=raw.decode(errors='replace')
    rec['verification_success']=rec['exit_status']==0 and 'VERIFICATION SUCCESSFUL' in s and 'VERIFICATION FAILED' not in s
    rec['receipt_normalization']='verification_success parsed from VERIFICATION SUCCESSFUL (the first launcher looked for a colon/hyphen spelling); source proof logs retained by hash'
    checks=re.findall(r'^\[([^\]]+)\].*: (SUCCESS|FAILURE|UNREACHABLE|UNDETERMINED)$',s,re.M)
    rec['checks_by_result']={v:sum(1 for _,a in checks if a==v) for v in sorted({v for _,v in checks})}
    rec['stdout_sha256']=hashlib.sha256(raw).hexdigest();rec['stdout_bytes']=len(raw)
    (dest/'receipt.json').write_text(json.dumps(rec,indent=2)+'\n')
    for f in ['stderr.log','time.log']:
        if (d/f).exists():shutil.copyfile(d/f,dest/f)
    if len(raw)<=131072:(dest/'stdout.log').write_bytes(raw)
    else:(dest/'stdout-excerpt.log').write_text(s[:4000]+'\n[Full log retained on host; SHA-256 and byte count in receipt]\n'+s[-8000:])
    rows.append(rec)
(export/'manifest.json').write_text(json.dumps({'schema':'r22-kani-proof-packet-v1','attempts':rows},indent=2)+'\n')
print(json.dumps({'attempts':len(rows),'passed':sum(r['verification_success'] for r in rows),'export':str(export)}))
