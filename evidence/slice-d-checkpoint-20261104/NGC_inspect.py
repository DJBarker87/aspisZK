"""Read-only source preflight. This script grants no proof or ledger credit."""
from pathlib import Path
import hashlib,json,subprocess
E=Path(__file__).resolve().parent
ROOT=E.parent.parent

def git(*args):
 return subprocess.check_output(['git',*args],cwd=ROOT)
def at(rev,path):return git('show',rev+':'+path)
def digest(data):return hashlib.sha256(data).hexdigest()
revision=git('rev-parse','HEAD').decode().strip()
prepare=git('rev-parse','codex/cx-slice-d-prepare-20261104').decode().strip()
frozen='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387'
paths=['crates/aspis-core/src/field.rs','crates/aspis-core/src/r0/heap.rs','crates/aspis-r1-cost-probe/src/verifier.rs','crates/aspis-r1-cost-probe/src/candidate.rs','crates/aspis-r1-cost-probe/src/transport.rs','programs/r1-cost-probe/src/lib.rs','Cargo.lock','evidence/slice-q-accum-20261104/NFS_QueryInvariant.lean','evidence/slice-q-accum-20261104/NFS_QueryLoopRoot.lean','evidence/slice-q-accum-20261104/NFS_PacketRoot.lean','evidence/kani-reverify5-20261028/KNE_Caller.lean','evidence/kani-reverify5-20261028/KNE_Leaf.lean','evidence/kani-reverify5-20261028/KNE_Final.lean','evidence/ledger7-20261104/NFX_COMBINED_IMPORT.lean','evidence/slice-d-check-20261104/NFU_BOUNDARIES.md']
pins=[]
for path in paths:
 data=at(revision,path)
 pin=dict(revision=revision,path=path,sha256=digest(data),bytes=len(data))
 if path.startswith(('crates/','programs/')) or path=='Cargo.lock':
  old=at(frozen,path);pin.update(frozen_revision=frozen,frozen_sha256=digest(old),byte_identical_to_frozen=old==data)
  assert old==data,path
 pins.append(pin)
for path in ['evidence/slice-d-prepare-20261104/NFW_CLOSED.json','evidence/slice-d-prepare-20261104/NFW_BRIDGES.md','evidence/slice-d-prepare-20261104/NFW_PreparedFields.lean']:
 data=at(prepare,path);pins.append(dict(revision=prepare,path=path,sha256=digest(data),bytes=len(data),usage='inspection only; no imported proof credit'))
candidate=at(revision,paths[3]).decode()
order=['let (mut a, pending) = query_loop','pending.finish(&mut a.weights);','let bytes = checkpoint(&p, &a, proof, public_bytes, hash);']
positions=[candidate.index(s) for s in order];assert positions==sorted(positions)
closed=json.loads(at(prepare,'evidence/slice-d-prepare-20261104/NFW_CLOSED.json'))
(E/'NGC_INPUT_PINS.json').write_text(json.dumps(dict(source_revision=revision,prepare_revision=prepare,inputs=pins),indent=2)+'\n')
(E/'NGC_SOURCE_REVIEW.json').write_text(json.dumps(dict(status='SOURCE-INSPECTION-ONLY',frozen_sources_equal=True,tx1_post_loop_order=order,prepare_closed_functions=[x['function'] for x in closed['functions']],ngc_new_closed_rows=0,compile_performed=False),indent=2)+'\n')
print('Source preflight passed; no proof/closure credit; pinned',len(pins),'inputs')
