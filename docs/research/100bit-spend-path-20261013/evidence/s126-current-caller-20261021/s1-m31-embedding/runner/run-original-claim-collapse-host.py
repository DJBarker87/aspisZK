#!/usr/bin/env python3
"""Reuse original nested claim LLBC with an isolated cached-source collapse identity-remap candidate.
No shipped source or LLBC edits. Extraction is not refinement or totality proof.
"""
from pathlib import Path
import json,hashlib,subprocess,os
H=Path('/home/dombarker/project-offloads/s126-real-sdk-20261021');src=Path('/home/dombarker/project-offloads/s1-current-claim-extraction-v2-20261020');W=H/'s1-collapse-tool-v3';T=W/'source';A=T/'src/_build/default/main.exe';tag='s1-original-claim-collapse-v1';O=H/tag;O.mkdir(exist_ok=False)
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest();llbc=src/'CurrentPowers.llbc';assert not json.loads(llbc.read_text())['has_errors']
cmd=[str(A),'-sequential','-no-progress-bar','-abort-on-error','-print-error-emitters','-loops-no-rec','-backend','lean','-namespace','AspisR1OriginalNestedClaim','-dest',str(O/'generated'),'-subdir','AspisR1OriginalNestedClaim','-split-files','-emit-json',str(llbc)]
subprocess.run(['python3',str(H/'kit/reservation.py'),str(H/(tag+'-admission.json'))],check=True,stdout=subprocess.DEVNULL)
patch=(W/'candidate.patch').read_bytes();(O/'tool.patch').write_bytes(patch)
(O/'input-lib.rs').write_bytes((src/'input/lib.rs').read_bytes())
(H/(tag+'-input.json')).write_text(json.dumps(dict(schema='focused-extractor-proof-packet-v1',command=cmd,tool_sha256=sha(A),tool_source_revision=json.loads((W/'input.json').read_text())['source_root_revision'],tool_patch_sha256=sha(O/'tool.patch'),tool_source_pins={n:sha(T/n) for n in ['src/interp/InterpJoin.ml','src/interp/InterpReduceCollapse.ml','src/PrePasses.ml']},llbc_sha256=sha(llbc),source_cut_sha256=sha(src/'input/lib.rs'),qualification=__doc__,expected_time='One focused original nested claim lowering from warm LLBC and an isolated freshly compiled identity-remap translator; no Rust rebuild, no Lean replay.'),indent=2)+'\n')
os.chdir(src/'input')
raise SystemExit(subprocess.call(['systemd-run','--user','--scope','-q','-p','MemoryHigh=6G','-p','MemoryMax=8G','-p','MemorySwapMax=0','-p','TasksMax=64','python3',str(H/'kit/capped.py'),str(H/'receipts'/tag),'Focused original nested claim with cached collapse/join fix; no source substitution','--','timeout','180',*cmd]))
