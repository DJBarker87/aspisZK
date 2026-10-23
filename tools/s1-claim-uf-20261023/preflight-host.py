#!/usr/bin/env python3
from pathlib import Path
import sys,os,json,hashlib,subprocess
H=Path('/home/dombarker/project-offloads/s126-real-sdk-20261021');mode=sys.argv[1];assert mode in ['positive','negative'];tag='s1-uf-'+mode+'-v1';P=H/'s1-uf-preflight-v1';T=Path('/home/dombarker/.kani/kani-0.67.0/bin/cbmc');Z=H/'z3-tool-v1/bin/z3';sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
os.environ['PATH']=str(Z.parent)+':/usr/bin:/bin';cmd=[str(T),str(P/'preflight.c'),'--z3','--unwind','16','--unwinding-assertions']+(['-DNEGATIVE'] if mode=='negative' else [])
subprocess.run(['python3',str(H/'kit/reservation.py'),str(H/(tag+'-admission.json'))],check=True,stdout=subprocess.DEVNULL)
(H/(tag+'-input.json')).write_text(json.dumps(dict(schema='focused-extractor-proof-packet-v1',command=cmd,source_sha256=sha(P/'preflight.c'),tool_pins={str(p):sha(p) for p in [T,Z]},expected='PASS' if mode=='positive' else 'FAIL at identity assertion',primary_reference='https://github.com/diffblue/cbmc/blob/8fcda333650440a60d3a054552a7ad318255b95d/regression/cbmc/uninterpreted_function/uf2.c',expected_time='Tiny UF semantics preflight, no project verifier or arithmetic proof.'),indent=2)+'\n')
raise SystemExit(subprocess.call(['systemd-run','--user','--scope','-q','-p','MemoryHigh=1G','-p','MemoryMax=2G','-p','MemorySwapMax=0','-p','TasksMax=32','python3',str(H/'kit/capped.py'),str(H/'receipts'/tag),'UF tool preflight and negative control; no source refinement claim','--','timeout','60',*cmd]))
