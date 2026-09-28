#!/usr/bin/env python3
"""Attribute actual wide-helper entries to immediately preceding call PCs."""
import argparse,bisect,collections,hashlib,json,mmap,struct
from pathlib import Path
p=argparse.ArgumentParser();p.add_argument('--stage',type=Path,required=True);a=p.parse_args();s=a.stage
analysis=json.loads((s/'full-trace/analysis.json').read_text());elf=s/'aspis-unstripped.so';data=elf.read_bytes();assert hashlib.sha256(data).hexdigest()==analysis['symbols_sha256']
def string(b,i):return b[i:b.index(0,i)].decode(errors='replace')
off=struct.unpack_from('<Q',data,40)[0];size,count,names=struct.unpack_from('<HHH',data,58);secs=[struct.unpack_from('<IIQQQQIIQQ',data,off+i*size)for i in range(count)]
ns=secs[names];ns=data[ns[4]:ns[4]+ns[5]];text=next(i for i,x in enumerate(secs)if string(ns,x[0])=='.text');base=secs[text][3]
symbols=[]
for sec in secs:
    if sec[1]!=2:continue
    st=secs[sec[6]];st=data[st[4]:st[4]+st[5]]
    for off in range(sec[4],sec[4]+sec[5],sec[9]):
        n,info,_,idx,value,length=struct.unpack_from('<IBBHQQ',data,off)
        if info&15==2 and idx==text:symbols.append(((value-base)//8,length//8,string(st,n)))
symbols.sort();starts=[x[0]for x in symbols];helper=next(x[0]for x in symbols if x[2]=='__multi3')
regs=Path(analysis['raw_trace']['regs']);calls=collections.Counter();previous=None
with regs.open('rb')as f,mmap.mmap(f.fileno(),0,access=mmap.ACCESS_READ)as b:
    for j in range(len(b)//96):
        pc=struct.unpack_from('<Q',b,j*96+88)[0]
        if pc==helper:
            i=bisect.bisect_right(starts,previous)-1;name=symbols[i][2]if i>=0 and previous<symbols[i][0]+symbols[i][1]else'(unmapped)'
            calls[(previous,name)]+=1
        previous=pc
report={'elf_sha256':analysis['elf_sha256'],'helper_entry_pc':helper,'helper_entries':sum(calls.values()),'callers':[{'pc':pc,'symbol':name,'calls':n}for(pc,name),n in calls.most_common()]}
out=s/'full-trace/helper-callers.json';assert not out.exists();out.write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(report,indent=2))
