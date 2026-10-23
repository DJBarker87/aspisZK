#!/usr/bin/env python3
"""Same source LLBC, formatting-only backend candidate; no semantic rewrite."""
from pathlib import Path
import hashlib,json,subprocess
H=Path('/home/dombarker/project-offloads/s126-real-sdk-20261021');P=H/'s6-full-forest-codec-five-unrolled-v1';q=P/'Codec-renamed.llbc'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
assert sha(q)==json.loads((P/'backend-renaming.json').read_text())['renamed_sha256']
A=H/'s6-formatter-tool-v3/source/src/_build/default/main.exe'
cmd=[str(A),'-sequential','-no-progress-bar','-abort-on-error','-print-error-emitters','-loops-no-rec','-backend','lean','-namespace','AspisS6FiveUnrolledCodec','-dest',str(P/'indent-generated'),'-subdir','AspisS6FiveUnrolledCodec','-split-files','-emit-json',str(q)]
tag='s6-full-forest-codec-five-unrolled-aeneas-indent-v1'
subprocess.run(['python3',str(H/'kit/reservation.py'),str(H/(tag+'-admission.json'))],check=True,stdout=subprocess.DEVNULL)
(H/(tag+'-input.json')).write_text(json.dumps(dict(schema='focused-extractor-proof-packet-v1',command=cmd,llbc_sha256=sha(q),tool_sha256=sha(A),renaming_sha256=sha(P/'backend-renaming.json'),qualification=__doc__,expected_time='Focused same-LLBC Aeneas translation with metadata-only collision resolution; no rebuild or arithmetic evaluation.'),indent=2)+'\n')
raise SystemExit(subprocess.call(['systemd-run','--user','--scope','-q','-p','MemoryHigh=6G','-p','MemoryMax=8G','-p','MemorySwapMax=0','-p','TasksMax=64','python3',str(H/'kit/capped.py'),str(H/'receipts'/tag),'Exact native outer codec: backend enum constructor naming only','--','timeout','180',*cmd]))
