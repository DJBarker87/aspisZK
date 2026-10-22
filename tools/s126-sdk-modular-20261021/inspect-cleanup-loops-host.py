#!/usr/bin/env python3
"""Metadata-only loop inspection of failed full cleanup enforcement; no replay."""
from pathlib import Path
import json,hashlib,subprocess
H=Path('/home/dombarker/project-offloads/s126-real-sdk-20261021');name='sdk-cleanup-stack-loop-inventory-v1';sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
ms=list((H/'target/kani').rglob('aspis_s126_sdk_ordered_cleanup_stack_frame_v1*.kani-metadata.json'));assert len(ms)==1
h=next(x for x in json.loads(ms[0].read_text())['proof_harnesses'] if x['pretty_name']=='proofs::actual_sdk_ordered_cleanup');program=Path(h['goto_file'].replace('.symtab.out','.out'));tool=Path('/home/dombarker/.kani/kani-0.67.0/bin/cbmc');cmd=[str(tool),'--show-loops','--json-ui',str(program)]
subprocess.run(['python3',str(H/'kit/reservation.py'),str(H/(name+'-admission.json'))],check=True,stdout=subprocess.DEVNULL)
(H/(name+'-input.json')).write_text(json.dumps(dict(command=cmd,program_sha256=sha(program),source_sha256=sha(H/'sdk-ordered-cleanup-stack-frame-v1/src/lib.rs'),metadata_sha256=sha(ms[0]),tool_sha256=sha(tool),runner_sha256=sha(Path(__file__)),qualification=__doc__),indent=2)+'\n')
status=subprocess.call(['systemd-run','--user','--scope','-q','-p','MemoryHigh=1G','-p','MemoryMax=2G','-p','MemorySwapMax=0','-p','TasksMax=64','python3',str(H/'kit/capped.py'),str(H/'receipts'/name),__doc__,'--',*cmd]);assert status==0
rows=json.loads((H/'receipts'/name/'stdout.log').read_text());print(json.dumps(rows)[:14000])
