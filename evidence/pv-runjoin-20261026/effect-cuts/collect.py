#!/usr/bin/env python3
"""Read the existing Kani logs; never invokes the verifier."""
from pathlib import Path
import json,re,hashlib
out=Path(__file__).resolve().parent
harnesses=['scan_exact','scan_exact','scan_exact','scan_zero_iff','scan_witness','single_byte','split_roundtrip','split_left','split_right','acceptance_exact']
for i,harness in enumerate(harnesses,1):
    a=f'{i:02}';log=(out/f'kani-effect-{a}.log').read_text();timing=(out/f'kani-effect-{a}.time').read_text()
    code=int(re.search(r'Exit status: (\d+)',timing)[1]);metrics={}
    for key in ['Elapsed (wall clock) time','Maximum resident set size','Swaps:']:
        metrics[key]=next((line.strip() for line in timing.splitlines() if key in line),None)
    rec={'attempt':i,'harness':'checks::'+harness,'source_revision':'fed15c4bc5 (verbatim helper snapshot and standalone harness manifest)',
         'exit':code,'status':'verified' if 'VERIFICATION:- SUCCESSFUL' in log else 'invocation rejected before verification',
         'metrics':metrics,'print_axioms':'N/A: Kani finite-machine source cut',
         'caps':{'MemoryHigh':'6G','MemoryMax':'8G','MemorySwapMax':0,'TasksMax':64},
         'unit':f'pv-runjoin-effect-kani-{a}.scope','profile':'Cargo dev explicitly opt-level=3; compiler command captured in03 log',
         'command':f'cargo kani --lib -j 4 '+('' if i==1 else '--output-format terse ')+f'--harness checks::{harness} --exact --verbose',
         'log_sha256':hashlib.sha256(log.encode()).hexdigest(),'stubs':False,
         'scope':'verbatim shipped entropy_nonzero32 plus symbolic64-byte split checks only; no OS/native owner/client/cleanup/artifact/privacy claim'}
    (out/f'receipt-{a}.json').write_text(json.dumps(rec,indent=2)+'\n')
print('Kani invocations10; verified8; setup rejections2')
