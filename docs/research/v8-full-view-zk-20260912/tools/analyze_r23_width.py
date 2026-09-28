#!/usr/bin/env python3
"""Compare existing clean traces; identify the same exact __multi3 leaf bytes."""
import argparse,hashlib,json,mmap,struct
from pathlib import Path
p=argparse.ArgumentParser()
for n in ['control','candidate','output']:p.add_argument('--'+n,type=Path,required=True)
a=p.parse_args()
def text(path):
    b=path.read_bytes();off=struct.unpack_from('<Q',b,40)[0];size,count,names=struct.unpack_from('<HHH',b,58)
    ss=[struct.unpack_from('<IIQQQQIIQQ',b,off+i*size)for i in range(count)];s=ss[names];names=b[s[4]:s[4]+s[5]]
    s=next(s for s in ss if names[s[0]:names.index(0,s[0])]==b'.text');return b[s[4]:s[4]+s[5]]
old=text(a.control/'sbf/aspis_v8_performance_sbf.so');needle=old[95186*8:(95186+43)*8]
assert hashlib.sha256(needle).hexdigest()=='9e0062594997b6e6a2864d0c25da2f52b97034ebfde566d428664d0aeb84af21'
new=text(a.candidate/'sbf/aspis_v8_performance_sbf.so');at=new.find(needle);assert at>=0 and at%8==0 and new.find(needle,at+1)<0
baseline=json.loads((a.control/'trace-analysis.json').read_text());candidate=json.loads((a.candidate/'trace-analysis.json').read_text());report={'guarded_sites':2,'helper_start_pc':at//8,'helper_byte_match':True,'modes':{}}
for mode in ['reference','scalar']:
    f=next((a.candidate/f'trace/{mode}-world0/registers').glob('*.regs'));entries=0;executed=0
    with f.open('rb')as f,mmap.mmap(f.fileno(),0,access=mmap.ACCESS_READ)as b:
        for i in range(0,len(b),96):
            pc=struct.unpack_from('<Q',b,i+88)[0];entries+=pc==at//8;executed+=at//8<=pc<(at+len(needle))//8
    x=baseline['runs'][mode];y=candidate['runs'][mode]
    report['modes'][mode]={'before_cu':x['cu'],'after_cu':y['cu'],'saved_cu':x['cu']-y['cu'],'saved_instructions':x['executed_instructions']-y['executed_instructions'],'helper_entries_after':entries,'helper_instructions_after':executed,'category_savings':{k:v-y['categories'].get(k,0)for k,v in x['categories'].items()}}
assert not a.output.exists();a.output.write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(report,indent=2))
