#!/usr/bin/env python3
"""Source-form GOTO inspection of actual successful native caller cleanup; no solver."""
from pathlib import Path
import json,subprocess,hashlib
H=Path('/home/dombarker/project-offloads/s126-real-sdk-20261021');tag='sdk-native-cleanup-goto-inventory-v1';P=H/'sdk-shared-prefix-success-bytes-pair-v1';program=H/'sdk-native-success-bytes-pair-v1/ready.out';tool=Path('/home/dombarker/.kani/kani-0.67.0/bin/goto-instrument');sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest();cmd=[str(tool),'--show-goto-functions',str(program)]
subprocess.run(['python3',str(H/'kit/reservation.py'),str(H/(tag+'-admission.json'))],check=True,stdout=subprocess.DEVNULL)
(H/(tag+'-input.json')).write_text(json.dumps(dict(command=cmd,program_sha256=sha(program),source_sha256=sha(P/'src/lib.rs'),tool_sha256=sha(tool),runner_sha256=sha(Path(__file__)),qualification=__doc__),indent=2)+'\n')
s=subprocess.call(['systemd-run','--user','--scope','-q','-p','MemoryHigh=1G','-p','MemoryMax=2G','-p','MemorySwapMax=0','-p','TasksMax=64','python3',str(H/'kit/capped.py'),str(H/'receipts'/tag),__doc__,'--',*cmd]);assert s==0
log=(H/'receipts'/tag/'stdout.log').read_text();rows=log.splitlines()
print('source_text_bytes',len(log))
for i,line in enumerate(rows):
 if line.startswith('adapter::stage1 /*'):print(i, '\n'.join(rows[max(i-2,0):i+8])[:3000])
