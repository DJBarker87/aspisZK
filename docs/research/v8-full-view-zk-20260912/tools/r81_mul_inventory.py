#!/usr/bin/env python3
"""Inspect operand reuse in an existing exact-text trace, not a new execution.
Only public verifier operands are recorded. Reconstruct bytes actually loaded
from the two incoming pointer arguments, and reject incomplete decoding.
"""
import argparse, bisect, collections, hashlib, json, mmap, struct
from pathlib import Path
p=argparse.ArgumentParser();p.add_argument('--stage',type=Path,required=True);p.add_argument('--output',type=Path,required=True);a=p.parse_args();s=a.stage
source=Path(__file__).with_name('analyze_r24_full_trace.py').read_text()
exec(source[source.index('def sha(p):'):source.index('traces=list(')])
analysis=json.loads((s/'full-trace/analysis.json').read_text())
assert analysis['exact_text_match'] and analysis['elf_sha256']==sha(deployed)
target=next((pc,pc+length,name)for pc,length,name in symbols if '::QM31::mul::'in name)
def owner(pc):
    i=bisect.bisect_right(starts,pc)-1
    assert i>=0 and pc<symbols[i][0]+symbols[i][1]
    return symbols[i][2].rsplit('::h',1)[0]
regs=Path(analysis['raw_trace']['regs']);insns=Path(analysis['raw_trace']['insns'])
assert sha(regs)==analysis['raw_trace']['regs_sha256'] and sha(insns)==analysis['raw_trace']['insns_sha256']
rows=[];active=None;prev=None
with regs.open('rb')as f,insns.open('rb')as g,mmap.mmap(f.fileno(),0,access=mmap.ACCESS_READ)as r,mmap.mmap(g.fileno(),0,access=mmap.ACCESS_READ)as b:
    for i in range(len(b)//8):
        rr=struct.unpack_from('<12Q',r,96*i);pc=rr[11];op,ds,off,imm=struct.unpack_from('<BBhi',b,8*i)
        if pc==target[0]:
            assert active is None and prev is not None and b[8*(i-1)]==0x85
            active={'caller':owner(prev),'pointers':[rr[2],rr[3]],'bytes':[[None]*16,[None]*16]}
        if active:
            assert target[0]<=pc<target[1]
            if op&7==1:
                addr=rr[ds>>4]+off;size={0:4,8:2,16:1,24:8}[op&24]
                loaded=struct.unpack_from('<Q',r,96*(i+1)+8*(ds&15))[0]
                for operand,start in enumerate(active['pointers']):
                    if start<=addr and addr+size<=start+16:
                        data=loaded.to_bytes(8,'little')[:size]
                        for j,v in enumerate(data):
                            old=active['bytes'][operand][addr-start+j]
                            assert old is None or old==v
                            active['bytes'][operand][addr-start+j]=v
            if op==0x95:
                assert all(v is not None for opbytes in active['bytes']for v in opbytes),active
                pair=tuple(tuple(struct.unpack('<4I',bytes(v)))for v in active['bytes'])
                assert all(v<2147483647 for operand in pair for v in operand)
                rows.append((active['caller'],pair));active=None
        prev=pc
assert active is None and len(rows)==1990
bycaller=collections.defaultdict(list)
for caller,pair in rows:bycaller[caller].append(pair)
def stats(pairs):
    unordered=[tuple(sorted(p))for p in pairs]
    return {'calls':len(pairs),'unique_commutative_pairs':len(set(unordered)),
        'same_operand':sum(a==b for a,b in pairs),
        'zero_operand':sum(any(all(x==0 for x in op)for op in p)for p in pairs),
        'one_operand':sum((1,0,0,0) in p for p in pairs),
        'M31_operand':sum(any(op[1:]==(0,0,0)for op in p)for p in pairs),
        'CM31_operand':sum(any(op[2:]==(0,0)for op in p)for p in pairs)}
report={'elf_sha256':sha(deployed),'trace_sha256':sha(s/'full-trace/analysis.json'),
    'scope':'one public world0 execution; operand bytes reconstructed from actual loads; not universal frequencies',
    'total':stats([p for _,p in rows]),'callers':{c:stats(p)for c,p in bycaller.items()}}
assert not a.output.exists();a.output.write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(report,indent=2))
