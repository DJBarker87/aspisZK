#!/usr/bin/env python3
"""Inspect unproved seed-contract property metadata; no solver replay or proof claim."""
from pathlib import Path
import json,subprocess,hashlib
H=Path('/home/dombarker/project-offloads/s126-real-sdk-20261021')
P=H/'sdk-seed-v2';proof=H/'receipts/sdk-seed-join-v2/receipt.json'
assert proof.is_file()
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
inputPin=H/'sdk-seed-join-v2-input.json'
assert json.loads(inputPin.read_text())['source_sha256']==sha(P/'src/lib.rs')
line=next(i+1 for i,s in enumerate((P/'src/lib.rs').read_text().splitlines()) if 'fn native_seed_byte_and_frame()' in s)
selected=[]
for metadata in (H/'target/kani').rglob('aspis_s126_sdk_seed*.kani-metadata.json'):
 for row in json.loads(metadata.read_text()).get('proof_harnesses',[]):
  if row['pretty_name']=='proofs::native_seed_byte_and_frame' and row['original_start_line']==line and row['attributes']['kind']=={'ProofForContract':{'target_fn':'native_seed'}}:
   selected.append((metadata,row))
assert len(selected)==1,selected
metadata,row=selected[0]
files=[Path(row['goto_file'].replace('.symtab.out','.out'))]
program=files[0];cbmc=Path('/home/dombarker/.kani/kani-0.67.0/bin/cbmc');tag='sdk-seed-properties-v3'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
subprocess.run(['python3',str(H/'kit/reservation.py'),str(H/(tag+'-admission.json'))],check=True,stdout=subprocess.DEVNULL)
cmd=[str(cbmc),'--show-properties','--json-ui',str(program)]
(H/(tag+'-input.json')).write_text(json.dumps(dict(schema='focused-extractor-proof-packet-v1',source_sha256=sha(P/'src/lib.rs'),proof_receipt_sha256=sha(proof),program_sha256=sha(program),tool_sha256=sha(cbmc),command=cmd,qualification=__doc__,harness_metadata_sha256=sha(metadata),harness_metadata=row,proof_input_sha256=sha(inputPin)),indent=2)+'\n')
out=H/'receipts'/tag
status=subprocess.call(['systemd-run','--user','--scope','-q','-p','MemoryHigh=1G','-p','MemoryMax=2G','-p','MemorySwapMax=0','-p','TasksMax=32','python3',str(H/'kit/capped.py'),str(out),'Read unproved seed-contract property locations; metadata only','--',*cmd]);assert status==0,status
items=json.loads((out/'stdout.log').read_text());props=[p for item in items for p in item.get('properties',[])]
selected=[p for p in props if p['class'] in ['cover','assigns']]
assert any(p['class']=='assigns' for p in selected)
assert sum(p['class']=='cover' for p in selected)==2
(out/'property-audit.json').write_text(json.dumps(dict(schema='focused-extractor-proof-packet-v1',total_properties=len(props),selected_properties=selected,source_sha256=sha(P/'src/lib.rs'),proof_receipt_sha256=sha(proof),program_sha256=sha(program),qualification='Property metadata only. The separately pinned seed check was stopped without a proof; this audit establishes no assertion or write-frame property.'),indent=2)+'\n')
print(json.dumps(dict(properties=len(props),selected=len(selected))))
