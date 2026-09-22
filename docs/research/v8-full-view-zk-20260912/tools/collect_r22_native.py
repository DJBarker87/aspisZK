#!/usr/bin/env python3
"""Collect compact R22 evidence; never copy keys, executables or large raw traces."""
import argparse, hashlib, json, re, shutil, struct, subprocess, mmap
from pathlib import Path
p=argparse.ArgumentParser()
for n in ['stage','profile','driver','symbol_elf','output']:p.add_argument('--'+n.replace('_','-'),type=Path,required=True)
a=p.parse_args();assert not a.output.exists();a.output.mkdir()
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def copy(src,dst):
    out=a.output/dst;out.parent.mkdir(parents=True,exist_ok=True);shutil.copy2(src,out)
for label,stage in [('clean',a.stage),('profile',a.profile)]:
    m=json.loads((stage/'r18-stage.json').read_text())
    assert len(m['files'])==179
    for n,h in m['files'].items():assert sha(stage/n)==h,n
    for n in ['r18-stage.json','r17-stage.json','r17-sbf-probe.json','sbf/compile.log','sbf/metadata.json','svm/receipt.json']:copy(stage/n,f'{label}/{n}')
    assert 'Exit status: 0' in (stage/'sbf/compile.log').read_text()
    receipt=json.loads((stage/'svm/receipt.json').read_text());assert receipt['elf_sha256']==sha(stage/'sbf/aspis_v8_performance_sbf.so')
    for mode in ['reference','scalar']:
        for world in range(2):
            stem=f'svm/{mode}-world{world}'
            for n in ['svm.jsonl','time.txt']:copy(stage/stem/n,f'{label}/{stem}/{n}')
            rows=[json.loads(l) for l in (stage/stem/'svm.jsonl').read_text().splitlines()]
            assert len(rows)==8
            for r in rows:
                assert not r['complete_aspis_verifier'] and r['heap_bytes']==262144 and not r['resource_failure']
                assert r['accepted'] if r['case']=='honest' else r['checked_rejection'] and not r['accepted']
for n in ['host/compile.log','host/check.log','host/metadata.json','host/generated/world0.bin','host/generated/world1.bin','trace-analysis.json']:copy(a.stage/n,'clean/'+n)
assert 'R22_NATIVE source_vectors=256 adjoint_basis_cases=4096 genuine_public_inputs=2' in (a.stage/'host/check.log').read_text()
for mode in ['reference','scalar']:
    for n in ['svm.jsonl','time.txt']:copy(a.stage/f'trace/{mode}-world0'/n,f'clean/trace/{mode}-world0/{n}')
for n in ['Cargo.toml','Cargo.lock','compile.log','resolution.log','added-tracing-packages.json','src/main.rs']:
    if (a.driver/n).exists():copy(a.driver/n,'driver/'+n)
for suffix,n in [('a','compile.log'),('b','resolution.log'),('c','compile.log'),('c','fetch.log')]:
    src=a.driver.with_name('aspis-r22-svm-20260922-'+suffix)/n
    copy(src,f'driver/preflight-{suffix}-{n}')
# A stripped executable has no function names. Attribute ONLY an exact, unique,
# relocation-free byte match to the named compiler builtin in the profile ELF.
objdump='/home/dombarker/.cache/solana/v1.54/platform-tools/llvm/bin/llvm-objdump'
syms=subprocess.check_output([objdump,'--syms',str(a.symbol_elf)],text=True)
line=next(l for l in syms.splitlines() if l.endswith(' __multi3'))
parts=line.split();address=int(parts[0],16);length=int(parts[-3],16)
def text_section(path):
    b=path.read_bytes();off=struct.unpack_from('<Q',b,40)[0];size,count,names=struct.unpack_from('<HHH',b,58)
    sections=[struct.unpack_from('<IIQQQQIIQQ',b,off+i*size) for i in range(count)]
    s=sections[names];strings=b[s[4]:s[4]+s[5]]
    t=next(s for s in sections if strings[s[0]:strings.index(0,s[0])]==b'.text')
    return b[t[4]:t[4]+t[5]],t[3]
profile,base=text_section(a.symbol_elf);needle=profile[address-base:address-base+length]
clean,_=text_section(a.stage/'sbf/aspis_v8_performance_sbf.so');at=clean.find(needle)
assert len(needle)==length and at>=0 and at%8==0 and clean.find(needle,at+1)<0
assert all(needle[i]!=0x85 for i in range(0,length,8)), 'must not transfer relocated call bytes'
helper={'symbol':'__multi3','symbol_line':line,'symbol_elf_sha256':sha(a.symbol_elf),'matched_bytes_sha256':hashlib.sha256(needle).hexdigest(),'unique_exact_byte_match':True,'clean_start_pc':at//8,'instructions':length//8,'counts':{},'caller_source_attribution':'not established'}
for mode in ['reference','scalar']:
    regs=next((a.stage/f'trace/{mode}-world0/registers').glob('*.regs'));counts=0;calls=0
    with regs.open('rb') as f,mmap.mmap(f.fileno(),0,access=mmap.ACCESS_READ) as b:
        for i in range(0,len(b),96):
            pc=struct.unpack_from('<Q',b,i+88)[0]
            counts+=at//8<=pc<(at+length)//8;calls+=pc==at//8
    helper['counts'][mode]={'executed_instructions':counts,'entries':calls}
(a.output/'helper-attribution.json').write_text(json.dumps(helper,indent=2)+'\n')
receipt={'decision':'retain native candidate; no production integration or total-CU claim','control_revision':'6f00e7f6c893c3a81bc37526e32d563434d303c8','research_base':'1c14e839c237085c96032e3a9a85ab2ad72f255a','native_stage':str(a.stage),'profile_stage':str(a.profile),'raw_traces_retained_on_build_host':True,'limits':{'build':'MemoryHigh=5G MemoryMax=7G MemorySwapMax=0 TasksMax=128','svm':'MemoryHigh=2G MemoryMax=3G MemorySwapMax=0 TasksMax=128'},'full_verifier_measured':False,'new_security_theorem':False}
(a.output/'receipt.json').write_text(json.dumps(receipt,indent=2)+'\n')
(a.output/'MANIFEST.json').write_text(json.dumps({str(f.relative_to(a.output)):sha(f) for f in sorted(a.output.rglob('*')) if f.is_file()},indent=2)+'\n')
print(json.dumps(helper,indent=2))
