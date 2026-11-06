"""Read-only frozen source identity check; no compiler or network execution."""
from pathlib import Path
import hashlib,json,subprocess
E=Path(__file__).resolve().parent;revision='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387';pins=json.loads((E/'NKE_SOURCE_PINS.json').read_text());rows=[];errors=[]
for name,want in pins.items():
 r=subprocess.run(['git','show',revision+':'+name],capture_output=True)
 got=hashlib.sha256(r.stdout).hexdigest() if r.returncode==0 else None
 rows.append({'path':name,'sha256':got,'expected':want,'same':got==want})
 if got!=want:errors.append(name)
lock=subprocess.check_output(['git','show',revision+':Cargo.lock']);lockhash=hashlib.sha256(lock).hexdigest()
status=subprocess.check_output(['git','status','--porcelain','--','crates','programs','Cargo.lock'],text=True)
out={'frozen_revision':revision,'files':len(rows),'all_same':not errors,'errors':errors,'files_checked':rows,'frozen_lock_sha256':lockhash,'worktree_shipped_status':status,'ELF_rebuild_trigger':bool(status),'ELF_pins':'inherited only; no rebuild claimed'}
(E/'NKE_FROZEN_SOURCE_CHECK.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps({k:out[k] for k in ['files','all_same','errors','frozen_lock_sha256','worktree_shipped_status','ELF_rebuild_trigger']}))
assert not errors and not status
