#!/usr/bin/env python3
"""Lower the forty affected declaration labels into the extended Site type.
This is a typed inventory, not a Calls tree or a source-coverage theorem.
"""
import argparse,hashlib,json
from pathlib import Path
R=Path(__file__).resolve().parents[2];B=R/'docs/research/100bit-spend-path-20261013';E=B/'evidence/s10-inventory4-20261021'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
rows=json.loads((B/'evidence/s10-inventory3-20261021/affected-declarations.json').read_text())
owners={r['name']:r['owner'] for r in json.loads((B/'evidence/s10-inventory2-20261021/mir-owners.json').read_text())}
constructors={**{'S'+str(i):'s'+str(i) for i in range(1,10)},'parser/codec':'parserCodec','multiproof':'multiproof','checkpoint ABI':'checkpointAbi','Pool caller':'poolCaller'}
lowered=[]
for r in rows:
    name=r['declaration'];owner=owners[name]
    if name=='aspis_core::r0::heap::filled':cone='.trustedStd'
    else:cone='.owned .'+constructors[owner]
    lowered.append(dict(id=r['id'],declaration=name,original_owner=owner,extended_owner=cone))
assert len(lowered)==40 and len({r['id'] for r in lowered})==40
assert sum(r['extended_owner']=='.trustedStd' for r in lowered)==1
text='''import OraclePortStdAllocation

/-! Forty affected declaration labels from the frozen compiler inventory.
This list is not the complete source driver and is not model_S10Join. -/
set_option autoImplicit false
namespace AspisR1.OraclePortS10InventoryStd
open OraclePortJoinSplitStd

def inventory : List Site := [
'''
text+=',\n'.join('  ⟨'+r['extended_owner']+', '+json.dumps(r['declaration'])+'⟩' for r in lowered)+']\n\n'
text+='''theorem heap_filled_mem : OraclePortStdAllocation.heapFilledSite ∈ inventory := by
  simp [inventory, OraclePortStdAllocation.heapFilledSite]

#print axioms heap_filled_mem
end AspisR1.OraclePortS10InventoryStd
'''
source=B/'lean/OraclePortS10InventoryStd.lean'
receipt=dict(schema='s10-pass4-owner-lowering-v1',records=lowered,declarations=40,site_compatible_owner_labels=40,exit_status=0,
    target='OraclePortJoinSplitStd.Site / Cone',
    scope='owner compatibility only; actual source tree, complete carriers, all continuation coverage and ordered caller identities remain open',
    inputs={str(p.relative_to(R)):sha(p) for p in [B/'evidence/s10-inventory3-20261021/affected-declarations.json',B/'evidence/s10-inventory2-20261021/mir-owners.json']},
    lean_source_sha256=hashlib.sha256(text.encode()).hexdigest())
raw=json.dumps(receipt,indent=2,sort_keys=True)+'\n';out=E/'owner-lowering.json'
p=argparse.ArgumentParser();p.add_argument('--check',action='store_true');a=p.parse_args()
if a.check:assert source.read_text()==text and out.read_text()==raw
else:source.write_text(text);out.write_text(raw)
print(json.dumps(dict(exit_status=0,declarations=40,typed_owners=40,source_coverage=False)))
