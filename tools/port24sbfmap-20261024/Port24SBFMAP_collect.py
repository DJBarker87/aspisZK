#!/usr/bin/env python3
"""Read only the released S10 re-pin3 snapshot and retained per-build artifacts.
Run on the host with python3 -; never access caches, tools, keys or other jobs.
"""
from pathlib import Path
import hashlib,json,re,resource,struct,time,sys,platform
start=time.monotonic()
H=Path('/home/dombarker/project-offloads/codex-cx-s10-repin3-20261023')
pins={}; result={'schema':'Port24SBFMAP-retained-selected-implementation-v1','root':str(H)}
def read(p):
    assert p.is_relative_to(H)
    assert not p.is_symlink(), str(p)
    b=p.read_bytes();pins[str(p)]={'sha256':hashlib.sha256(b).hexdigest(),'bytes':len(b)};return b
def js(p): return json.loads(read(p))
def section_table(b):
    assert b[:6]==b'\x7fELF\x02\x01'
    h=struct.unpack_from('<16sHHIQQQIHHHHHH',b)
    ss=[struct.unpack_from('<IIQQQQIIQQ',b,h[6]+i*h[11]) for i in range(h[12])]
    st=ss[h[13]]; names=b[st[4]:st[4]+st[5]]
    return {names[s[0]:names.index(b'\0',s[0])].decode():s for s in ss},ss
def functions(lines,pat,kind):
    out=[];i=0
    while i<len(lines):
        if lines[i].startswith('define ' if kind=='llvm' else 'fn ') and re.search(pat,lines[i]):
            a=i
            while i<len(lines) and lines[i]!='}':i+=1
            text='\n'.join(lines[a:i+1])+'\n'
            out.append({'start':a+1,'end':i+1,'header':lines[a], 'sha256':hashlib.sha256(text.encode()).hexdigest(),'text':text})
        i+=1
    return out
manifest=js(H/'source-inputs.json');result['source_revision']=manifest['source_revision']
selected=['Cargo.lock','programs/r1-cost-probe/src/lib.rs','programs/aspis-pool/src/lib.rs','programs/aspis-pool/src/entrypoint.rs','crates/aspis-core/src/r0/heap.rs','crates/aspis-r1-cost-probe/src/verifier.rs','programs/aspis-pool/src/processor.rs','crates/aspis-core/src/field/qm31.rs','crates/aspis-core/src/field.rs']
result['sources']=[]
for rel in selected:
    row=next((x for x in manifest['files'] if x['path']==rel),None)
    if not row:continue
    p=H/'src'/rel;b=read(p);assert pins[str(p)]['sha256']==row['sha256']
    lines=b.decode().splitlines()
    if rel=='Cargo.lock':
        text='\n'.join(x for block in b.decode().split('[[package]]') if re.search(r'name = "(solana-program|solana-program-entrypoint)"',block) for x in ('[[package]]'+block).splitlines())
    elif rel.endswith(('verifier.rs','processor.rs')):
        text='\n'.join(f'{i+1}: {x}' for i,x in enumerate(lines) if re.search('Accumulator|try_reserve_exact|resize|Allocation|Vec::new|fn new|entrypoint!',x) or (rel.endswith('verifier.rs') and 203<=i<=230))
    else:text=b.decode()
    result['sources'].append({'path':str(p),'pin':row,'text':text})
result['builds']={}
for mode in ['default','devnet','pool']:
    d=H/f'build-{mode}-v1';r={'command':js(d/'command.json'),'comparison':js(d/'artifact-comparison.json'),'original_receipt':js(d/'receipt/receipt.json')}
    r['diagnostic_commands']={str(f):js(f) for f in sorted((d/'diagnostics').glob('*.command.json'))}
    dep=d/'artifacts'/('aspis_pool.so' if mode=='pool' else 'aspis_r1_cost_probe_program.so')
    db=read(dep);lb=read(d/'linked.elf');ds,_=section_table(db);ss,sections=section_table(lb)
    def sec(b,s):return b[s[4]:s[4]+s[5]]
    assert sec(db,ds['.text'])==sec(lb,ss['.text'])
    r['elf']={'deployed':pins[str(dep)],'linked':pins[str(d/'linked.elf')],'text_equal':True,'text_sha256':hashlib.sha256(sec(db,ds['.text'])).hexdigest(),'sections':{n:{'address':s[3],'bytes':s[5]} for n,s in ss.items()}}
    r['elf']['comments']={n:sec(lb,s).decode(errors='replace') for n,s in ss.items() if n=='.comment'}
    symbols=[]
    for sn in ['.symtab','.dynsym']:
        s=ss.get(sn)
        if not s:continue
        st=sec(lb,sections[s[6]])
        for pos in range(s[4],s[4]+s[5],24):
            name,info,other,idx,addr,size=struct.unpack_from('<IBBHQQ',lb,pos)
            n=st[name:st.index(b'\0',name)].decode()
            if re.search(r'heap6filled|raw_vec.*(finish_grow|try_reserve_exact)|___rust_alloc|__rust_alloc|BumpAllocator|Accumulator.*3new|BatchedWeights.*3new|rust_no_alloc_shim',n):
                row={'table':sn,'name':n,'address':addr,'bytes':size,'section_index':idx,'info':info}
                if size and idx<len(sections):
                    se=sections[idx];raw=lb[se[4]+addr-se[3]:se[4]+addr-se[3]+size];row['machine_sha256']=hashlib.sha256(raw).hexdigest()
                    if 'rust_alloc' in n and size<2048:
                        row['instructions']=[{'address':addr+i,'opcode':raw[i],'registers':raw[i+1],'offset':struct.unpack_from('<h',raw,i+2)[0],'imm':struct.unpack_from('<i',raw,i+4)[0]} for i in range(0,len(raw),8)]
                symbols.append(row)
    r['selected_elf_symbols']=symbols
    r['ir']=[];r['mir']=[];r['mono']=[]
    for f in sorted((d/'compiler-output').glob('*.ll')):
        ls=read(f).decode().splitlines()
        # Core and the root program retain different concrete specializations.
        pat=r'heap6filled|RawVecInner.*try_reserve_exact|raw_vec11finish_grow|___rustc12___rust_alloc\(|Accumulator.*3new|BatchedWeights.*3new|___rustc26___rust_alloc_error_handler|rust_no_alloc_shim_is_unstable_v2'
        fs=functions(ls,pat,'llvm')
        r['ir'].append({'path':str(f),'declarations':[x for x in ls if x.startswith('declare ') and re.search('rust_alloc|rust_no_alloc|abort',x)],'identity':[x for x in ls if x.startswith(('target datalayout','target triple')) or re.search(r'!\d+ = !\{!"rustc',x)],'functions':fs})
    for f in sorted((d/'compiler-output').glob('*.mir')):
        if not ('aspis_core-' in f.name or 'aspis_r1_cost_probe' in f.name or f.name=='aspis_pool.mir'):continue
        ls=read(f).decode().splitlines()
        r['mir'].append({'path':str(f),'functions':functions(ls,r'^fn heap::filled(?:\(|::)|^fn .*verifier.rs:(9[0-9]|20[0-9]):.*::(new|from_weights)|^fn __rust_alloc','mir')})
    for f in sorted((d/'diagnostics').glob('*.mono.txt')):
        ls=read(f).decode().splitlines()
        pattern=r'alloc::alloc::Global|RawVecInner::(grow_exact|try_reserve_exact|set_ptr_and_cap)|r0::heap::filled|Accumulator::new|Vec::<\[u64; 4\]>'
        r['mono'].append({'path':str(f),'lines':[{'line':i+1,'text':x} for i,x in enumerate(ls) if re.search(pattern,x)]})
    result['builds'][mode]=r
result['inputs']=pins
u=resource.getrusage(resource.RUSAGE_SELF)
result['inspection_receipt']={'command':['python3','-'],'python':sys.version,'platform':platform.platform(),'exit_status':0,'wall_seconds':time.monotonic()-start,'peak_rss_kib':u.ru_maxrss,'swaps':u.ru_nswap,'source_revision':result['source_revision'],'print_axioms':'N/A: read-only Python source/ELF/IR inspection; no formal proof','script_sha256':None}
print(json.dumps(result,indent=2))
