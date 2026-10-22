#!/usr/bin/env python3
"""Inspect already proved fixed-size copy contract properties; no solver replay."""
from pathlib import Path
import json,subprocess,hashlib,sys
H=Path('/home/dombarker/project-offloads/s126-real-sdk-20261021')
version=sys.argv[1] if len(sys.argv)>1 else 'v3';assert version in ['v3','v4','v5']
P=H/('sdk-finish-fixed-frame-'+version);proof=H/('receipts/sdk-finish-fixed-frame-join-'+version+'/receipt.json')
assert json.loads(proof.read_text())['exit_status']==0
files=[p for p in (H/'target/kani').rglob('*aspis_s126_sdk_finish_fixed_frame*exact_finish_fixed_frame*.out') if not p.name.endswith('.symtab.out')]
files=[p for p in files if any(r['pretty_name']=='proofs::exact_finish_fixed_frame' and r['original_start_line']==next(i+1 for i,line in enumerate((P/'src/lib.rs').read_text().splitlines()) if 'fn exact_finish_fixed_frame()' in line) for r in json.loads((p.parent/(p.name.split('__',1)[0]+'.kani-metadata.json')).read_text())['proof_harnesses'])]
assert len(files)==1,files
program=files[0];cbmc=Path('/home/dombarker/.kani/kani-0.67.0/bin/cbmc');tag='sdk-finish-fixed-frame-properties-'+version
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
subprocess.run(['python3',str(H/'kit/reservation.py'),str(H/(tag+'-admission.json'))],check=True,stdout=subprocess.DEVNULL)
cmd=[str(cbmc),'--show-properties','--json-ui',str(program)]
(H/(tag+'-input.json')).write_text(json.dumps(dict(schema='focused-extractor-proof-packet-v1',source_sha256=sha(P/'src/lib.rs'),proof_receipt_sha256=sha(proof),program_sha256=sha(program),tool_sha256=sha(cbmc),command=cmd,qualification=__doc__),indent=2)+'\n')
out=H/'receipts'/tag
status=subprocess.call(['systemd-run','--user','--scope','-q','-p','MemoryHigh=1G','-p','MemoryMax=2G','-p','MemorySwapMax=0','-p','TasksMax=32','python3',str(H/'kit/capped.py'),str(out),'Read proved SDK fixed-size copy assigns/postcondition properties; no solver replay','--',*cmd]);assert status==0,status
items=json.loads((out/'stdout.log').read_text());props=[p for item in items for p in item.get('properties',[])]
selected=[p for p in props if p['class'] in ['assigns','cover'] or 'expected' in p['description']]
assert any(p['class']=='assigns' for p in selected)
assert any('expected' in p['description'] for p in selected)
(out/'property-audit.json').write_text(json.dumps(dict(schema='focused-extractor-proof-packet-v1',total_properties=len(props),selected_properties=selected,source_sha256=sha(P/'src/lib.rs'),proof_receipt_sha256=sha(proof),program_sha256=sha(program),qualification='Property metadata only; solver result is the separately pinned successful proof-for-contract receipt.'),indent=2)+'\n')
print(json.dumps(dict(properties=len(props),selected=len(selected))))
