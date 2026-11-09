#!/usr/bin/env python3
"""Transparent frozen-rustc wrapper: retain mono items, MIR and LLVM IR.
No source/optimization flags change. ELF equality is checked independently.
"""
import json,os,shutil,subprocess,sys
from pathlib import Path
real,*args=sys.argv[1:]
selected={'aspis_core','aspis_statement','aspis_r1_cost_probe','aspis_r1_cost_probe_program','aspis_pool'}
crate=args[args.index('--crate-name')+1] if '--crate-name' in args else ''
if crate in selected:
    for i,arg in enumerate(args):
        if arg.startswith('--emit='):
            args[i]=arg+',llvm-ir,mir'
    args+=['-Zprint-mono-items=yes']
    out=Path(os.environ['S10_DIAGNOSTICS']);out.mkdir(parents=True,exist_ok=True)
    with (out/(crate+'.command.json')).open('w') as f:json.dump([real,*args],f,indent=2)
    with (out/(crate+'.mono.txt')).open('w') as stdout:
        status=subprocess.run([real,*args],stdout=stdout).returncode
    if status==0 and '--out-dir' in args:
        retained=out/'compiler-output';retained.mkdir(exist_ok=True)
        for p in Path(args[args.index('--out-dir')+1]).iterdir():
            if p.suffix in ('.ll','.mir') and (p.stem==crate or p.name.startswith(crate+'-')):
                shutil.copy2(p,retained/p.name)
    sys.exit(status)
os.execv(real,[real,*args])
