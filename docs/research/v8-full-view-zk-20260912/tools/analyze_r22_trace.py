#!/usr/bin/env python3
"""Executed SBPF-v0 opcode/PC attribution; not a source-level cost guess."""
import argparse,bisect,collections,hashlib,json,mmap,struct
from pathlib import Path
p=argparse.ArgumentParser();p.add_argument('--stage',type=Path,required=True);a=p.parse_args()
elf=a.stage/'sbf/aspis_v8_performance_sbf.so';data=elf.read_bytes()
def sha(p):
    h=hashlib.sha256()
    with p.open('rb')as f:
        for b in iter(lambda:f.read(1048576),b''):h.update(b)
    return h.hexdigest()
assert data[:6]==b'\x7fELF\x02\x01'
flags=struct.unpack_from('<I',data,48)[0]
assert flags==0, f'Opcode classification supports observed SBPF v0 only, got flags={flags}'
off=struct.unpack_from('<Q',data,40)[0];size,count,names=struct.unpack_from('<HHH',data,58)
sections=[struct.unpack_from('<IIQQQQIIQQ',data,off+i*size)for i in range(count)]
name_bytes=data[sections[names][4]:sections[names][4]+sections[names][5]]
def string(b,i):return b[i:b.index(0,i)].decode('utf8',errors='replace')
text_index=next(i for i,s in enumerate(sections)if string(name_bytes,s[0])=='.text');base=sections[text_index][3]
symbols=[]
def demangle(s):
    if not s.startswith('_ZN'):return s
    rest=s[3:];parts=[]
    while rest and rest[0].isdigit():
        j=0
        while j<len(rest)and rest[j].isdigit():j+=1
        n=int(rest[:j]);parts.append(rest[j:j+n]);rest=rest[j+n:]
    return '::'.join(parts) if parts else s
for section in sections:
    if section[1]!=2:continue
    names_section=sections[section[6]];strings=data[names_section[4]:names_section[4]+names_section[5]]
    for pos in range(section[4],section[4]+section[5],section[9]):
        name,info,other,sec,value,length=struct.unpack_from('<IBBHQQ',data,pos)
        if info&15==2 and sec==text_index and value>=base:symbols.append(((value-base)//8,demangle(string(strings,name)),length//8))
symbols.sort();starts=[s[0]for s in symbols]
def category(op):
    kind=op&7;upper=op&0xf0
    if kind==0:return 'immediate_load'
    if kind==1:return 'memory_load'
    if kind in (2,3):return 'memory_store'
    if kind in (4,7):
        return {0:'add_sub',0x10:'add_sub',0x20:'integer_multiply',0x30:'integer_divide',0x90:'integer_remainder',0x60:'shift',0x70:'shift',0xc0:'shift',0xb0:'move',0x40:'bitwise',0x50:'bitwise',0xa0:'bitwise'}.get(upper,'other_alu')
    if kind==5:return 'call' if upper==0x80 else ('exit' if upper==0x90 else 'branch')
    return 'other'
report={'elf_sha256':sha(elf),'elf_flags':flags,'scope':'clean native ordinary+image, executed instructions','functions_have_inline_work':True,'runs':{}}
for mode in ['reference','scalar']:
    dest=a.stage/f'trace/{mode}-world0';traces=list((dest/'registers').glob('*.insns'));assert len(traces)==1
    insns=traces[0];regs=insns.with_suffix('.regs');assert regs.stat().st_size==12*insns.stat().st_size
    assert insns.with_suffix('.exec.sha256').read_text().strip()==sha(elf)
    ops=collections.Counter();pcs=collections.Counter();functions=collections.Counter();pc_instruction={}
    with insns.open('rb')as f,regs.open('rb')as r,mmap.mmap(f.fileno(),0,access=mmap.ACCESS_READ)as ib,mmap.mmap(r.fileno(),0,access=mmap.ACCESS_READ)as rb:
        for i in range(len(ib)//8):
            op=ib[8*i];pc=struct.unpack_from('<Q',rb,96*i+88)[0]
            ops[op]+=1;pcs[pc]+=1;pc_instruction[pc]=ib[8*i:8*i+8].hex()
        for pc,n in pcs.items():
            index=bisect.bisect_right(starts,pc)-1
            name=symbols[index][1] if index>=0 and (symbols[index][2]==0 or pc<symbols[index][0]+symbols[index][2]) else '(unmapped)'
            functions[name]+=n
    cats=collections.Counter()
    for op,n in ops.items():cats[category(op)]+=n
    row=json.loads((dest/'svm.jsonl').read_text());assert row['accepted'] and row['register_tracing']
    clean=[json.loads(l)for l in (a.stage/f'svm/{mode}-world0/svm.jsonl').read_text().splitlines()]
    assert row['cu']==next(r['cu']for r in clean if r['case']=='honest'and r['cap']==row['cap'])
    report['runs'][mode]={'cu':row['cu'],'executed_instructions':sum(ops.values()),'categories':dict(cats),'opcode_counts':{f'0x{k:02x}':v for k,v in sorted(ops.items())},'function_counts':functions.most_common(),
        'top_pcs':[{'pc':pc,'count':n,'instruction_hex':pc_instruction[pc]}for pc,n in pcs.most_common(24)],
        'raw_trace_sha256':{'insns':sha(insns),'regs':sha(regs)},'tracing_cu_matches_clean':True}
left=report['runs']['reference'];right=report['runs']['scalar']
report['reference_minus_scalar']={'cu':left['cu']-right['cu'],'executed_instructions':left['executed_instructions']-right['executed_instructions'],
    'categories':{k:left['categories'].get(k,0)-right['categories'].get(k,0)for k in set(left['categories'])|set(right['categories'])}}
out=a.stage/'trace-analysis.json';assert not out.exists();out.write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps({'runs':{k:{x:v[x]for x in ['cu','executed_instructions','categories']}for k,v in report['runs'].items()},'delta':report['reference_minus_scalar']},indent=2))
