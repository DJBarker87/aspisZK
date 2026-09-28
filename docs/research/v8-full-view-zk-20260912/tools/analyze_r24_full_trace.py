#!/usr/bin/env python3
"""Exact executed-PC attribution using byte-identical unstripped text symbols."""
import argparse,bisect,collections,hashlib,json,mmap,struct
from pathlib import Path
p=argparse.ArgumentParser();p.add_argument('--stage',type=Path,required=True);a=p.parse_args();s=a.stage
def sha(p):
    h=hashlib.sha256()
    with p.open('rb')as f:
        for b in iter(lambda:f.read(1048576),b''):h.update(b)
    return h.hexdigest()
def string(b,i):return b[i:b.index(0,i)].decode(errors='replace')
def elf(path):
    data=path.read_bytes();assert data[:6]==b'\x7fELF\x02\x01' and struct.unpack_from('<I',data,48)[0]==0
    off=struct.unpack_from('<Q',data,40)[0];size,count,names=struct.unpack_from('<HHH',data,58)
    secs=[struct.unpack_from('<IIQQQQIIQQ',data,off+i*size)for i in range(count)]
    names=secs[names];names=data[names[4]:names[4]+names[5]]
    text=next(i for i,x in enumerate(secs)if string(names,x[0])=='.text');t=secs[text]
    return data,secs,text,t[3],data[t[4]:t[4]+t[5]]
deployed=s/'sbf-primary/aspis_v8_performance_sbf.so';symbols_path=s/'aspis-unstripped.so'
_,_,_,base,code=elf(deployed);data,secs,text,symbol_base,symbol_code=elf(symbols_path)
assert base==symbol_base and code==symbol_code,'not the exact compiled text'
def demangle(n):
    if not n.startswith('_ZN'):return n
    rest=n[3:];parts=[]
    while rest and rest[0].isdigit():
        j=0
        while j<len(rest)and rest[j].isdigit():j+=1
        length=int(rest[:j]);parts.append(rest[j:j+length]);rest=rest[j+length:]
    return '::'.join(parts)if parts else n
symbols=[]
for sec in secs:
    if sec[1]!=2:continue
    strings=secs[sec[6]];strings=data[strings[4]:strings[4]+strings[5]]
    for off in range(sec[4],sec[4]+sec[5],sec[9]):
        n,info,_,idx,value,length=struct.unpack_from('<IBBHQQ',data,off)
        if info&15==2 and idx==text and value>=base:symbols.append(((value-base)//8,length//8,demangle(string(strings,n))))
symbols.sort();assert symbols;starts=[x[0]for x in symbols]
traces=list((s/'full-trace/registers').glob('*.insns'));assert len(traces)==1;insns=traces[0];regs=insns.with_suffix('.regs')
assert regs.stat().st_size==12*insns.stat().st_size
assert insns.with_suffix('.exec.sha256').read_text().strip()==sha(deployed)
ops=collections.Counter();pcs=collections.Counter()
with insns.open('rb')as i,regs.open('rb')as r,mmap.mmap(i.fileno(),0,access=mmap.ACCESS_READ)as ib,mmap.mmap(r.fileno(),0,access=mmap.ACCESS_READ)as rb:
    for j in range(len(ib)//8):ops[ib[8*j]]+=1;pcs[struct.unpack_from('<Q',rb,96*j+88)[0]]+=1
counts=collections.Counter();entries=collections.Counter()
for pc,n in pcs.items():
    i=bisect.bisect_right(starts,pc)-1
    name=symbols[i][2]if i>=0 and pc<symbols[i][0]+symbols[i][1]else '(unmapped)'
    counts[name]+=n
    if i>=0 and pc==symbols[i][0]:entries[name]+=n
def category(op):
    kind=op&7;upper=op&0xf0
    if kind==0:return 'immediate_load'
    if kind==1:return 'memory_load'
    if kind in (2,3):return 'memory_store'
    if kind in (4,7):return {0:'add_sub',0x10:'add_sub',0x20:'integer_multiply',0x30:'divide',0x90:'remainder',0x60:'shift',0x70:'shift',0xc0:'shift',0xb0:'move',0x40:'bitwise',0x50:'bitwise',0xa0:'bitwise'}.get(upper,'other_alu')
    if kind==5:return 'call'if upper==0x80 else('exit'if upper==0x90 else'branch')
    return 'other'
cats=collections.Counter()
for op,n in ops.items():cats[category(op)]+=n
receipt=json.loads((s/'full-trace/receipt.json').read_text());assert receipt['clean_cu_equal']
report={'elf_sha256':sha(deployed),'symbols_sha256':sha(symbols_path),'exact_text_match':True,'scope':'complete verifier, world0, exclusive function instruction counts; inline work remains in caller','cu':receipt['result']['cu'],'executed_instructions':sum(ops.values()),'categories':dict(cats),'functions':[{'name':name,'instructions':n,'entries':entries[name]}for name,n in counts.most_common()],'raw_trace':{'insns':str(insns),'insns_sha256':sha(insns),'regs':str(regs),'regs_sha256':sha(regs)},'top_pcs':pcs.most_common(32)}
out=s/'full-trace/analysis.json';assert not out.exists();out.write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps({k:v[:25]if k=='functions'else v for k,v in report.items()if k not in ['raw_trace','top_pcs']},indent=2))
