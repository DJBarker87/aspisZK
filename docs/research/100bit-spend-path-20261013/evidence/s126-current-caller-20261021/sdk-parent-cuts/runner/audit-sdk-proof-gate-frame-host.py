#!/usr/bin/env python3
"""Inspect already proved proof-gate contract properties; no solver replay."""
from pathlib import Path
import json,subprocess,hashlib
H=Path('/home/dombarker/project-offloads/s126-real-sdk-20261021')
P=H/'sdk-proof-gate-v3';proof=H/'receipts/sdk-proof-gate-frame-v1/receipt.json'
assert json.loads(proof.read_text())['exit_status']==0
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
inputPin=H/'sdk-proof-gate-frame-v1-input.json'
assert json.loads(inputPin.read_text())['source_sha256']==sha(P/'src/lib.rs')
line=next(i+1 for i,s in enumerate((P/'src/lib.rs').read_text().splitlines()) if 'fn actual_sdk_guard_reference()' in s)
selected=[]
for metadata in (H/'target/kani').rglob('aspis_s126_sdk_proof_gate*.kani-metadata.json'):
 for row in json.loads(metadata.read_text()).get('proof_harnesses',[]):
  if row['pretty_name']=='proofs::actual_sdk_guard_reference' and row['original_start_line']==line and row['attributes']['kind']=={'ProofForContract':{'target_fn':'native_gate'}}:
   selected.append((metadata,row))
assert len(selected)==1,selected
metadata,row=selected[0]
files=[Path(row['goto_file'].replace('.symtab.out','.out'))]
program=files[0];cbmc=Path('/home/dombarker/.kani/kani-0.67.0/bin/cbmc');tag='sdk-proof-gate-frame-properties-v2'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
subprocess.run(['python3',str(H/'kit/reservation.py'),str(H/(tag+'-admission.json'))],check=True,stdout=subprocess.DEVNULL)
cmd=[str(cbmc),'--show-properties','--json-ui',str(program)]
(H/(tag+'-input.json')).write_text(json.dumps(dict(schema='focused-extractor-proof-packet-v1',source_sha256=sha(P/'src/lib.rs'),proof_receipt_sha256=sha(proof),program_sha256=sha(program),tool_sha256=sha(cbmc),command=cmd,qualification=__doc__,harness_metadata_sha256=sha(metadata),harness_metadata=row,proof_input_sha256=sha(inputPin)),indent=2)+'\n')
out=H/'receipts'/tag
status=subprocess.call(['systemd-run','--user','--scope','-q','-p','MemoryHigh=1G','-p','MemoryMax=2G','-p','MemorySwapMax=0','-p','TasksMax=32','python3',str(H/'kit/capped.py'),str(out),'Read proved stage1 guard and cover locations; no solver replay','--',*cmd]);assert status==0,status
items=json.loads((out/'stdout.log').read_text());props=[p for item in items for p in item.get('properties',[])]
selected=[p for p in props if p['class'] in ['cover','assigns']]
assert any(p['class']=='assigns' for p in selected)
assert sum(p['class']=='cover' for p in selected)==5
(out/'property-audit.json').write_text(json.dumps(dict(schema='focused-extractor-proof-packet-v1',total_properties=len(props),selected_properties=selected,source_sha256=sha(P/'src/lib.rs'),proof_receipt_sha256=sha(proof),program_sha256=sha(program),qualification='Property metadata only; solver result is the separately pinned successful proof-for-contract receipt.'),indent=2)+'\n')
print(json.dumps(dict(properties=len(props),selected=len(selected))))
