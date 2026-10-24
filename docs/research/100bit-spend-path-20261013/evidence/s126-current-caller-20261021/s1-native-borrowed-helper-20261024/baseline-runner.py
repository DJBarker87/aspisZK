#!/usr/bin/env python3
from pathlib import Path
import json,hashlib,os,subprocess
H=Path('/home/dombarker/project-offloads/s126-real-sdk-20261021');S=H/'s1-claim-owned-nested-v10';W=H/'s1-borrowed-helper-baseline-v1-20261024';W.mkdir(exist_ok=False)
raw=json.loads((S/'ClaimOwned.llbc').read_text());assert not raw['has_errors']
subprocess.run(['python3',str(H/'kit/reservation.py'),str(W/'admission.json')],check=True,stdout=subprocess.DEVNULL)
snap=subprocess.check_output(['python3','/home/dombarker/project-offloads/r1-circle-sample-wrapper-extraction-v2/collect-cgroups.py'],text=True);(W/'global-admission.json').write_text(snap);m=json.loads(snap);G=2**30;assert m['effective_sum_bytes']+2*G<=48*G and m['MemAvailable_kB']*1024>=4*G
A=Path('/home/dombarker/project-offloads/v7-tag73-challenge-qm31-source-20260825-work/toolchain/output/aeneas-b59d5188-lean432-extended-static')
cmd=[str(A),'-sequential','-no-progress-bar','-abort-on-error','-print-error-emitters','-loops-no-rec','-backend','lean','-namespace','AspisS1OwnedNestedClaim','-dest',str(W/'generated'),'-subdir','AspisS1OwnedNestedClaim','-split-files','-emit-json',str(S/'ClaimOwned.llbc')]
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest();(W/'input.json').write_text(json.dumps(dict(schema='focused-extractor-proof-packet-v1',command=cmd,source_sha256=sha(S/'input/lib.rs'),llbc_sha256=sha(S/'ClaimOwned.llbc'),tool_sha256=sha(A),runner_sha256=sha(Path(__file__)),has_errors=raw['has_errors'],qualification='Baseline pinned Aeneas on retained borrowed-helper reference LLBC; no tool patch or repeated Charon job. Source and LLBC hashes identify the input; LLBC is not distributed.'),indent=2)+'\n')
os.environ['PATH']='/home/dombarker/.cargo/bin:/usr/bin:/bin'
raise SystemExit(subprocess.call(['systemd-run','--user','--scope','-q','-p','MemoryHigh=1G','-p','MemoryMax=2G','-p','MemorySwapMax=0','-p','TasksMax=32','python3',str(H/'kit/capped.py'),str(W/'attempt'),'Focused original baseline Aeneas translation of borrowed-helper reference; no arithmetic evaluation','--',*cmd]))
