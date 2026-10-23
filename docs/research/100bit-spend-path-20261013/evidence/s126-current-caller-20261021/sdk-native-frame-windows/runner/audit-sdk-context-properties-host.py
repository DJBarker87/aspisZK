#!/usr/bin/env python3
"""Pin full native caller property inventory before dividing solver obligations."""
from pathlib import Path
import json,hashlib,subprocess
H=Path('/home/dombarker/project-offloads/s126-real-sdk-20261021')
tag='sdk-native-context-properties-v4';program=H/'sdk-native-context-check-v5/ready.out'
source=H/'sdk-native-context-v4/src/lib.rs';tool=Path('/home/dombarker/.kani/kani-0.67.0/bin/cbmc')
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
cmd=[str(tool),'--show-properties','--json-ui',str(program)]
subprocess.run(['python3',str(H/'kit/reservation.py'),str(H/(tag+'-admission.json'))],check=True,stdout=subprocess.DEVNULL)
(H/(tag+'-input.json')).write_text(json.dumps(dict(schema='focused-extractor-proof-packet-v1',command=cmd,source_sha256=sha(source),program_sha256=sha(program),tool_sha256=sha(tool),qualification=__doc__),indent=2)+'\n')
out=H/'receipts'/tag
status=subprocess.call(['systemd-run','--user','--scope','-q','-p','MemoryHigh=1G','-p','MemoryMax=2G','-p','MemorySwapMax=0','-p','TasksMax=32','python3',str(H/'kit/capped.py'),str(out),'Read full native context properties; no solver replay','--',*cmd]);assert status==0,status
items=json.loads((out/'stdout.log').read_text());props=[p for item in items for p in item.get('properties',[])]
(out/'property-inventory.json').write_text(json.dumps(dict(schema='focused-extractor-proof-packet-v1',properties=props,source_sha256=sha(source),program_sha256=sha(program),qualification='Inventory only, no assertion established.'),indent=2)+'\n')
print(json.dumps(dict(properties=len(props))))
