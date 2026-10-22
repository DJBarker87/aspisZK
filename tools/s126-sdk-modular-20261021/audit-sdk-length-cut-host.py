#!/usr/bin/env python3
"""Audit contract/frame and unreachable comparison in the all-wrong-length cut.
Metadata inspection only; the pinned solver receipt supplies verification.
"""
from pathlib import Path
import json,hashlib,subprocess
H=Path('/home/dombarker/project-offloads/s126-real-sdk-20261021')
tag='sdk-proof-length-frame-properties-v2';proof='sdk-proof-length-frame-cut-v2'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
source=H/'sdk-proof-gate-v4/src/lib.rs';inp=H/(proof+'-input.json')
pin=json.loads(inp.read_text());assert pin['source_sha256']==sha(source)
program=H/proof/'ready.out';receipt=H/'receipts'/proof/'receipt.json'
r=json.loads(receipt.read_text());assert r['exit_status']==10 and r['swaps']==0
rows=json.loads((H/proof/'properties-without-traces.json').read_text())
assert all(p['status']=='SUCCESS' for p in rows if p['sourceLocation'].get('propertyClass')!='cover')
assert any(p['status']=='SUCCESS' and p['property'].startswith('memcmp.') for p in rows)
cmd=['/home/dombarker/.kani/kani-0.67.0/bin/cbmc','--show-properties','--json-ui',str(program)]
subprocess.run(['python3',str(H/'kit/reservation.py'),str(H/(tag+'-admission.json'))],check=True,stdout=subprocess.DEVNULL)
(H/(tag+'-input.json')).write_text(json.dumps(dict(schema='focused-extractor-proof-packet-v1',source_sha256=sha(source),proof_input_sha256=sha(inp),proof_receipt_sha256=sha(receipt),program_sha256=sha(program),command=cmd,tool_sha256=sha(Path(cmd[0])),qualification=__doc__),indent=2)+'\n')
out=H/'receipts'/tag
status=subprocess.call(['systemd-run','--user','--scope','-q','-p','MemoryHigh=1G','-p','MemoryMax=2G','-p','MemorySwapMax=0','-p','TasksMax=32','python3',str(H/'kit/capped.py'),str(out),'Read all-wrong-length checked source contract frame properties; no solver replay','--',*cmd]);assert status==0
items=json.loads((out/'stdout.log').read_text());props=[p for item in items for p in item.get('properties',[])]
selected=[p for p in props if p['class'] in ['assigns','cover'] or p['name'].startswith('memcmp.')]
assert any(p['class']=='assigns' for p in selected)
assert len([p for p in selected if p['class']=='cover'])==2
assert any(p['name'].startswith('memcmp.') for p in selected)
(out/'property-audit.json').write_text(json.dumps(dict(schema='focused-extractor-proof-packet-v1',source_sha256=sha(source),proof_receipt_sha256=sha(receipt),program_sha256=sha(program),total_properties=len(props),selected_properties=selected,qualification=__doc__),indent=2)+'\n')
print(json.dumps(dict(properties=len(props),selected=len(selected))))
