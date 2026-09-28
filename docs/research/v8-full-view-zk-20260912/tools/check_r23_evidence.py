#!/usr/bin/env python3
"""Offline R23 receipt/source integrity audit; no unchanged expensive replay."""
import argparse,hashlib,json
from pathlib import Path
p=argparse.ArgumentParser();p.add_argument('--native-assembled',type=Path);p.add_argument('--control',type=Path);a=p.parse_args();root=Path(__file__).resolve().parent.parent;e=root/'evidence/r23-width'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
m=json.loads((e/'MANIFEST.json').read_text())
for n,h in m.items():assert sha(e/n)==h,n
assert not any('keypair' in n or n.endswith(('.so','.regs','.insns'))for n in m)
native=json.loads((e/'native/r18-stage.json').read_text());full=json.loads((e/'full/r18-stage.json').read_text())
assert len(native['files'])==182 and len(full['files'])==174
assert sha(root/'tools/r23_width.rs')==full['files']['crates/aspis-core/src/r23_width.rs']==sha(e/'r23_width.rs')
for n in ['crates/aspis-core/src/field.rs','crates/aspis-core/src/r23_width.rs']:assert native['files'][n]==full['files'][n]
if a.native_assembled:
    for n,h in native['files'].items():assert sha(a.native_assembled/n)==h,n
if a.control:
    old=json.loads((a.control/'r18-stage.json').read_text());assert len(old['files'])==173
    for n,h in old['files'].items():assert sha(a.control/n)==h,n
    assert {n for n,h in old['files'].items()if full['files'][n]!=h}=={'crates/aspis-core/src/field.rs'}
    assert set(full['files'])-set(old['files'])=={'crates/aspis-core/src/r23_width.rs'}
    # Local reconstructed controls retain the exact source pins but may have
    # different staging-path metadata. Authenticate the original manifest too.
    frozen=root/'evidence/r20-clean-b/r18-stage.json'
    assert old['files']==json.loads(frozen.read_text())['files']
    assert full['r23_width']['control_manifest_sha256']==sha(frozen)
receipt=json.loads((e/'full/r23-svm-a/receipt.json').read_text());assert receipt['full_verifier'] and not receipt['scalar_transpose_installed']
for r,cu in zip(receipt['runs'],[2529453,2530968]):
    assert len(r['results'])==4
    for x in r['results']:
        assert x['heap_bytes']==262144 and x['unchanged_accounts']
        if x['cu_limit']==1000000:assert x['resource_failure'] and not x['accepted'] and not x['custom_rejection']
        elif x['case']=='honest':assert x['accepted'] and x['cu']==cu
        else:assert x['custom_rejection'] and not x['accepted'] and not x['resource_failure']
controls=json.loads((e/'full/r23-host-a/wire-controls/results.json').read_text())
assert len(controls['cases'])==3281 and sum(x['checked_rejection']for x in controls['cases'])==3280
analysis=json.loads((e/'native/r23-width-analysis.json').read_text())
assert [analysis['modes'][x]['helper_entries_after']for x in ['reference','scalar']]==[4,4]
print(json.dumps({'status':'PASS','evidence_files':len(m),'native_pins':182,'full_pins':174,'only_two_field_sites_changed':True,'wire_controls':3281,'full_cu':[2529453,2530968],'one_million_gate':'FAIL: resource exhaustion, not checked rejection','native_assembled_checked':bool(a.native_assembled),'control_checked':bool(a.control)},indent=2))
