#!/usr/bin/env python3
"""Attribute retained arithmetic leaf execution to actual predecessor call PCs.
Consumes an existing exact-text trace; never reruns the verifier.
"""
import argparse,collections,json,mmap,struct
from pathlib import Path
p=argparse.ArgumentParser();p.add_argument('--stage',type=Path,required=True);p.add_argument('--output',type=Path,required=True);a=p.parse_args();s=a.stage
source=Path(__file__).with_name('analyze_r24_full_trace.py').read_text()
start=source.index('def sha(p):');end=source.index('traces=list(')
import bisect,hashlib
exec(source[start:end])
analysis=json.loads((s/'full-trace/analysis.json').read_text())
assert analysis['exact_text_match'] and analysis['elf_sha256']==sha(deployed)
target_names={'aspis_core::field::QM31::mul','aspis_core::field::PreparedQm31Multiplier::mul','aspis_core::field::r25_checked_dot'}
def plain(n):return n.rsplit('::h',1)[0]
targets={pc:(pc+length,name)for pc,length,name in symbols if plain(name) in target_names}
assert len(targets)==3
def owner(pc):
    i=bisect.bisect_right(starts,pc)-1
    assert i>=0 and pc<symbols[i][0]+symbols[i][1],pc
    return symbols[i][2]
regs=Path(analysis['raw_trace']['regs']);insns=Path(analysis['raw_trace']['insns'])
assert sha(regs)==analysis['raw_trace']['regs_sha256'] and sha(insns)==analysis['raw_trace']['insns_sha256']
assert regs.stat().st_size==12*insns.stat().st_size
calls=collections.Counter();costs=collections.Counter();active=None;prev=None
with regs.open('rb')as f,insns.open('rb')as g,mmap.mmap(f.fileno(),0,access=mmap.ACCESS_READ)as r,mmap.mmap(g.fileno(),0,access=mmap.ACCESS_READ)as b:
    for i in range(len(b)//8):
        pc=struct.unpack_from('<Q',r,96*i+88)[0];op=b[8*i]
        if pc in targets:
            assert active is None and prev is not None and b[8*(i-1)]==0x85,(i,pc,active)
            end,name=targets[pc];key=(name,owner(prev),prev);calls[key]+=1
            active=(pc,end,key)
        if active:
            begin,end,key=active
            assert begin<=pc<end,'unexpected nested call; do not misattribute it'
            costs[key]+=1
            if op==0x95:active=None
        prev=pc
assert active is None
rows=[{'callee':plain(k[0]),'caller':plain(k[1]),'call_pc':k[2],'calls':n,'exclusive_instructions':costs[k]}
    for k,n in sorted(calls.items(),key=lambda x:-costs[x[0]])]
for name in target_names:
    old=next(x for x in analysis['functions']if plain(x['name'])==name)
    assert sum(x['calls']for x in rows if x['callee']==name)==old['entries']
    assert sum(x['exclusive_instructions']for x in rows if x['callee']==name)==old['instructions']
report={'base_revision':'6af7c8384ccea9dce41e16075cd29f77179bd8a0','elf_sha256':sha(deployed),
    'trace_analysis_sha256':sha(s/'full-trace/analysis.json'),'source_line_attribution':False,
    'scope':'world0 retained exact-text trace; exclusive leaf instructions attributed to predecessor call PCs',
    'calls':rows}
assert not a.output.exists();a.output.write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps(report,indent=2))
