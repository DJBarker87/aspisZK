#!/usr/bin/env python3
"""Inspect the stopped real-guard comparison's pointer analysis; no proof.
No solver replay and no export of the retained compiled input.
"""
from pathlib import Path
import json,hashlib,subprocess
H=Path('/home/dombarker/project-offloads/s126-real-sdk-20261021')
tag='sdk-live-alias-inspection-v1';program=H/tag/'input.out'
tool=Path('/home/dombarker/.kani/kani-0.67.0/bin/goto-instrument')
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
subprocess.run(['python3',str(H/'kit/reservation.py'),str(H/(tag+'-admission.json'))],check=True,stdout=subprocess.DEVNULL)
cmd=[str(tool),'--show-value-sets',str(program)]
(H/(tag+'-input.json')).write_text(json.dumps(dict(schema='focused-extractor-proof-packet-v1',program_sha256=sha(program),tool_sha256=sha(tool),runner_sha256=sha(Path(__file__)),command=cmd,qualification=__doc__),indent=2)+'\n')
raise SystemExit(subprocess.call(['systemd-run','--user','--scope','-q','-p','MemoryHigh=1G','-p','MemoryMax=2G','-p','MemorySwapMax=0','-p','TasksMax=32','python3',str(H/'kit/capped.py'),str(H/'receipts'/tag),'Read pointer value sets of stopped comparison; no SMT/SAT search','--',*cmd]))
