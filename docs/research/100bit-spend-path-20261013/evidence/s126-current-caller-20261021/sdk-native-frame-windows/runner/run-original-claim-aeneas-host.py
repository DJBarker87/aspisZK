#!/usr/bin/env python3
from pathlib import Path
import hashlib,json,os,subprocess,sys
H=Path('/home/dombarker/project-offloads/s126-real-sdk-20261021');src=Path('/home/dombarker/project-offloads/s1-current-claim-extraction-v2-20261020');tag=sys.argv[1];mode=sys.argv[2];assert mode in ['-loops-no-rec','-loops-to-rec']
A=Path('/home/dombarker/project-offloads/v7-tag73-challenge-qm31-source-20260825-work/toolchain/output/aeneas-b59d5188-lean432-extended-static');out=H/tag;out.mkdir(exist_ok=False);llbc=src/'CurrentPowers.llbc';x=json.loads(llbc.read_text());assert not x['has_errors']
cmd=[str(A),'-sequential','-no-progress-bar','-abort-on-error','-print-error-emitters',mode,'-backend','lean','-namespace','AspisR1OriginalNestedClaim','-dest',str(out/'generated'),'-subdir','AspisR1OriginalNestedClaim','-split-files','-emit-json',str(llbc)]
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
subprocess.run(['python3',str(H/'kit/reservation.py'),str(H/(tag+'-admission.json'))],check=True,stdout=subprocess.DEVNULL)
(H/(tag+'-input.json')).write_text(json.dumps(dict(command=cmd,tool_sha256=sha(A),llbc_sha256=sha(llbc),source_cut_sha256=sha(src/'input/lib.rs'),qualification='Reuse of byte-pinned original nested-claim LLBC, different loop emission mode. No source change, compiler change or assertion bypass.'),indent=2)+'\n')
os.chdir(src/'input')
raise SystemExit(subprocess.call(['systemd-run','--user','--scope','-q','-p','MemoryHigh=6G','-p','MemoryMax=8G','-p','MemorySwapMax=0','-p','TasksMax=64','python3',str(H/'kit/capped.py'),str(H/'receipts'/tag),'Focused original nested-claim lowering from warm validated LLBC, no Rust/Lean rebuild','--',*cmd]))
