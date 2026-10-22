#!/usr/bin/env python3
"""Inspect already proved byte-step contract properties; no solver replay."""
from pathlib import Path
import json,subprocess,hashlib
H=Path('/home/dombarker/project-offloads/s126-real-sdk-20261021')
P=H/'sdk-finish-step-v3';proof=H/'receipts/sdk-finish-step-join-v3/receipt.json'
assert json.loads(proof.read_text())['exit_status']==0
files=[p for p in (H/'target/kani').rglob('*aspis_s126_sdk_finish_step*actual_sdk_copy_step_frame*.out') if not p.name.endswith('.symtab.out')]
assert len(files)==1,files
program=files[0];cbmc=Path('/home/dombarker/.kani/kani-0.67.0/bin/cbmc');tag='sdk-finish-step-properties-v3'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
subprocess.run(['python3',str(H/'kit/reservation.py'),str(H/(tag+'-admission.json'))],check=True,stdout=subprocess.DEVNULL)
cmd=[str(cbmc),'--show-properties','--json-ui',str(program)]
(H/(tag+'-input.json')).write_text(json.dumps(dict(schema='focused-extractor-proof-packet-v1',source_sha256=sha(P/'src/lib.rs'),proof_receipt_sha256=sha(proof),program_sha256=sha(program),tool_sha256=sha(cbmc),command=cmd,qualification=__doc__),indent=2)+'\n')
out=H/'receipts'/tag
status=subprocess.call(['systemd-run','--user','--scope','-q','-p','MemoryHigh=1G','-p','MemoryMax=2G','-p','MemorySwapMax=0','-p','TasksMax=32','python3',str(H/'kit/capped.py'),str(out),'Read proved SDK byte-step assigns/postcondition properties; no solver replay','--',*cmd]);assert status==0,status
items=json.loads((out/'stdout.log').read_text());props=[p for item in items for p in item.get('properties',[])]
selected=[p for p in props if p['class']=='assigns' or 'old(' in p['description']]
assert any(p['class']=='assigns' for p in selected)
assert any('old(' in p['description'] for p in selected)
(out/'property-audit.json').write_text(json.dumps(dict(schema='focused-extractor-proof-packet-v1',total_properties=len(props),selected_properties=selected,source_sha256=sha(P/'src/lib.rs'),proof_receipt_sha256=sha(proof),program_sha256=sha(program),qualification='Property metadata only; solver result is the separately pinned successful proof-for-contract receipt.'),indent=2)+'\n')
print(json.dumps(dict(properties=len(props),selected=len(selected))))
