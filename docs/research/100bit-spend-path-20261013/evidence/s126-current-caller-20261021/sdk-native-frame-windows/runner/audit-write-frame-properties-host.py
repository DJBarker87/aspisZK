#!/usr/bin/env python3
"""Read the checked GOTO property's assign/ensures metadata; no solver replay.
Only text property metadata and binary hashes are exported, not binaries.
"""
from pathlib import Path
import os,sys,subprocess,json,hashlib
H=Path('/home/dombarker/project-offloads/s126-real-sdk-20261021');name=sys.argv[1]
assert name in ['shared','exclusive']
version=sys.argv[2] if len(sys.argv)>2 else 'v1';assert version in ['v1','v2','v3']
input_tag='sdk-'+name+'-properties'+('' if version=='v1' else '-'+version)
crate=H/('sdk-'+name+'-write-frame-'+version);receipt=H/'receipts'/('sdk-'+name+'-write-frame-'+version)
passed=json.loads((receipt/'receipt.json').read_text());assert passed['exit_status']==0
files=[p for p in (H/'target/kani').rglob('*.out') if not p.name.endswith('.symtab.out') and 'aspis_s126_sdk_shared_write_frame' in p.name and ('actual_sdk_'+name+'_write_frame') in p.name]
assert len(files)==1,files
program=files[0];cbmc=Path('/home/dombarker/.kani/kani-0.67.0/bin/cbmc');out=H/'receipts'/('sdk-'+name+'-write-properties-'+version)
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
(H/(input_tag+'-input.json')).write_text(json.dumps(dict(schema='focused-extractor-proof-packet-v1',checked_receipt_sha256=sha(receipt/'receipt.json'),checked_source_sha256=sha(crate/'src/lib.rs'),program_path=str(program),program_sha256=sha(program),tool_sha256=sha(cbmc),qualification=__doc__),indent=2)+'\n')
prior=json.loads((out/'property-audit.json').read_text()) if (out/'property-audit.json').exists() else None
reuse=prior is not None and prior['source_sha256']==sha(crate/'src/lib.rs') and prior['checked_program_sha256']==sha(program)
if not reuse:
 subprocess.run(['python3',str(H/'kit/reservation.py'),str(H/(input_tag+'-admission.json'))],check=True,stdout=subprocess.DEVNULL)
 cmd=[str(cbmc),'--show-properties','--json-ui',str(program)]
 status=subprocess.call(['systemd-run','--user','--scope','-q','-p','MemoryHigh=1G','-p','MemoryMax=2G','-p','MemorySwapMax=0','-p','TasksMax=32','python3',str(H/'kit/capped.py'),str(out),'Read already checked GOTO property metadata; no compiler or solver replay','--',*cmd])
 assert status==0,status
items=json.loads((out/'stdout.log').read_text());props=[p for item in items for p in item.get('properties',[])]
interesting=[p for p in props if any(word in json.dumps(p).lower() for word in ['assigns','write_set','write set','ensures','contract','counter','old('])]
summary=dict(schema='focused-extractor-proof-packet-v1',total_properties=len(props),contract_properties=interesting,source_sha256=sha(crate/'src/lib.rs'),checked_program_sha256=sha(program),qualification='Property metadata inspection only. Solver result is the pinned original proof-for-contract receipt; no independent proof claimed.')
(out/'property-audit.json').write_text(json.dumps(summary,indent=2)+'\n')
print(json.dumps(dict(properties=len(props),contract_properties=len(interesting))))
