#!/usr/bin/env python3
"""Count actual predecessor PCs for the byte-identified R22 __multi3 leaf."""
import argparse,collections,hashlib,json,mmap,struct
from pathlib import Path
p=argparse.ArgumentParser();p.add_argument('--stage',type=Path,required=True);p.add_argument('--output',type=Path,required=True);a=p.parse_args()
report={'source_attribution':'caller PCs only; no source-line inference','runs':{}}
for mode in ['reference','scalar']:
    regs=next((a.stage/f'trace/{mode}-world0/registers').glob('*.regs'));insns=regs.with_suffix('.insns')
    calls=collections.Counter();prev=None
    with regs.open('rb')as f,insns.open('rb')as g,mmap.mmap(f.fileno(),0,access=mmap.ACCESS_READ)as r,mmap.mmap(g.fileno(),0,access=mmap.ACCESS_READ)as b:
        for i in range(len(b)//8):
            pc=struct.unpack_from('<Q',r,96*i+88)[0]
            if pc==95186:
                assert prev is not None and b[8*(i-1)]==0x85
                calls[prev]+=1
            prev=pc
    report['runs'][mode]={'total_entries':sum(calls.values()),'callers':calls.most_common(),'regs_sha256':hashlib.sha256(regs.read_bytes()).hexdigest()}
assert report['runs']['reference']['total_entries']==2887
assert report['runs']['scalar']['total_entries']==3088
assert not a.output.exists();a.output.write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(report,indent=2))
