#!/usr/bin/env python3
"""Finite ELF audit. Fail closed on unknown instruction/call/inline provenance.
No theorem or whole-program noninterference certificate is produced.
"""
from pathlib import Path
import subprocess,re,json,hashlib,lzma,sys,collections
D=Path(sys.argv[1]); B=Path(sys.argv[2]); D.mkdir(exist_ok=True)
def save(name,value): (D/name).write_text(json.dumps(value,indent=2)+'\n')
def run(name,args):
    s=subprocess.check_output(args,text=True); (D/name).write_text(s); return s
sym=run('symbols.txt',['nm','-S','-n','-C',str(B)])
sec=run('sections.txt',['readelf','-SW',str(B)])
rel=run('relocations.txt',['readelf','-rW',str(B)])
asm=run('disassembly.txt',['objdump','-d','-C','--no-show-raw-insn',str(B)])
func={}
for s in sym.splitlines():
    m=re.match(r'([\da-f]+) ([\da-f]+) ([tTwW]) (.*)',s)
    if m:
        a,n=int(m[1],16),int(m[2],16)
        if n: func.setdefault(a,dict(address=hex(a),end=hex(a+n),size=n,names=[],instructions=[]))['names'].append(m[4])
cur=None
for s in asm.splitlines():
    m=re.match(r'^([\da-f]+) <(.*)>:',s)
    if m: cur=func.get(int(m[1],16));continue
    m=re.match(r'\s*([\da-f]+):\s+([a-z][a-z\d_.]*)\s*(.*)',s)
    if cur is not None and m and int(m[1],16)<int(cur['end'],16):
        cur['instructions'].append(dict(address=hex(int(m[1],16)),op=m[2],args=m[3],text=s.strip()))
relocs={int(m[1],16):int(m[2],16) for m in re.finditer(r'^([\da-f]+)\s+\S+\s+R_X86_64_RELATIVE\s+([\da-f]+)\s*$',rel,re.M)}
def target(i):
    a=i['args']
    if not a.startswith('*'):
        m=re.match(r'([\da-f]+)\s+<',a);return int(m[1],16) if m else None
    # RIP-relative GOT references carry the slot address in objdump's comment.
    m=re.search(r'#\s+([\da-f]+)',a)
    return relocs.get(int(m[1],16)) if m else None
edges=[]; unresolved=[]
for a,f in func.items():
    for i in f['instructions']:
        if i['op'] in ['call','jmp']:
            t=target(i)
            if t in func and t!=a: edges.append(dict(caller=hex(a),site=i['address'],target=hex(t),instruction=i['text'],resolution='R_X86_64_RELATIVE/GOT' if i['args'].startswith('*') else 'direct'))
            elif i['args'].startswith('*'):unresolved.append(dict(caller=hex(a),**i))
# Selection deliberately broad, not an inference that all selected functions run.
selected={a:f for a,f in func.items() if any((n.startswith('<aspis_core::field::') and 'Debug' not in n and 'from_le_bytes' not in n and 'write_le_bytes' not in n) or n.startswith('aspis_core::field::qm31_m31_dot') or ('aspis_r1_cost_probe::host_semantic::' in n and any(x in n for x in ['build_with_material','copy_endpoint_values','copy_tuple_limb'])) for n in f['names'])}
# Aliases: track a full physical register, including subregisters conservatively.
def reg(s):
    s=s.lstrip('%')
    if re.match(r'r\d+[bwd]?$',s): return re.sub('[bwd]$','',s)
    for full,forms in [('rax',['rax','eax','ax','al','ah']),('rbx',['rbx','ebx','bx','bl','bh']),('rcx',['rcx','ecx','cx','cl','ch']),('rdx',['rdx','edx','dx','dl','dh']),('rsi',['rsi','esi','si','sil']),('rdi',['rdi','edi','di','dil']),('rbp',['rbp','ebp','bp','bpl']),('rsp',['rsp','esp','sp','spl'])]:
        if s in forms:return full
    return s
R=re.compile(r'%([a-z][a-z\d]*)')
def operands(a):return re.split(r',\s*(?![^()]*\))',a.split('#')[0].strip()) if a.split('#')[0].strip() else []
def regs(x):return {reg(r) for r in R.findall(x)}
def analyze(f):
    ins=f['instructions'];name=f['names'][0]
    # All incoming field data are secret; argument addresses, lengths, exponents
    # and public layout start public. Every non-stack non-RIP load is tainted.
    initial=({'rdi'} if name=='<aspis_core::field::M31>::inv' else {'rdi','rsi'} if name=='<aspis_core::field::CM31>::pow' else {'rsi'} if '::from_m31' in name else set())
    # Host aggregate ABI is not reconstructed; no CLEAN possible there.
    host='host_semantic::' in name
    at={i['address']:j for j,i in enumerate(ins)};states={0:(initial,set(),False)};q=collections.deque([0]);seen=set();alerts={};unknown={};tainted_ops={};rounds=0
    def emit(out,i,why):out[(i['address'],why)]=dict(instruction=i['text'],reason=why)
    while q:
        j=q.popleft();T,M,F=states[j];T=set(T);M=set(M);i=ins[j];op=i['op'];args=operands(i['args']);rounds+=1
        if rounds>100000:emit(unknown,i,'fixpoint bound');break
        def read(x):
            if '(' in x:
                rr=regs(x)
                if rr=={'rip'}:return False
                if rr<= {'rsp','rbp'}:return x in M
                return True
            return bool(regs(x)&T)
        def write(x,v):
            if '(' in x:
                if regs(x)<= {'rsp','rbp'}:
                    if v:M.add(x)
                    else:M.discard(x)
            elif x.startswith('%'):
                r=reg(x)
                if v:T.add(r)
                else:T.discard(r)
        isbranch=op.startswith('j') and op!='jmp'
        if isbranch and F:emit(alerts,i,'tainted conditional branch')
        if op in ['call','jmp'] and i['args'].startswith('*') and regs(i['args'].split('#')[0])&T:emit(alerts,i,'tainted indirect target/address')
        if op not in ['lea','nop','nopl','nopw']:
            for x in args:
                if '(' in x and regs(x)&T:emit(alerts,i,'tainted memory address')
        latency=bool(re.match(r'(?:i?div|v?divs[sd]|v?sqrts[sd]|bsf|bsr|pdep|pext|rdrand|rdseed)',op))
        if latency and any(read(x) for x in args):emit(alerts,i,'tainted operand to latency-review instruction')
        if any(read(x) for x in args):tainted_ops[op]=tainted_ops.get(op,0)+1
        zero=len(args)==2 and args[0]==args[1] and op in ['xor','pxor','xorps','xorpd','vpxor','pcmpeqd']
        if op in ['ret','int3','nop','nopl','nopw','endbr64']:pass
        elif op=='push':pass # stack movement does not change spill taint names
        elif op=='pop':write(args[-1],False)
        elif op.startswith('mov') and len(args)==2:write(args[1],read(args[0]))
        elif op=='lea' and len(args)==2:write(args[1],bool(regs(args[0])&T))
        elif op in ['cmp','test'] and len(args)==2:F=any(read(x) for x in args)
        elif op.startswith('cmov') and len(args)==2:write(args[1],F or any(read(x) for x in args))
        elif op.startswith('set') and len(args)==1:write(args[0],F)
        elif zero:write(args[-1],False);F=False if op=='xor' else F
        elif op in ['call']:
            emit(unknown,i,'callee effects/ABI not composed');T.update(['rax','rcx','rdx','rsi','rdi','r8','r9','r10','r11']);F=True
        elif op=='jmp' or isbranch:pass
        elif op in ['add','sub','and','or','xor','adc','sbb','shl','shr','sar','sal','rol','ror','neg','not','inc','dec','imul','mul','paddd','psubd','pand','pandn','por','pxor','pcmpeqd','pcmpgtd','pshufd','punpckldq','punpcklqdq','punpckhdq','psrlq','psrld','psllq','pslld','pmuludq','pmulld','pblendw','shufps','unpcklps','unpckhps','xorps','xorpd'] and args:
            v=any(read(x) for x in args) or (F and op in ['adc','sbb'])
            write(args[-1],v)
            if op in ['add','sub','and','or','xor','adc','sbb','shl','shr','sar','sal','rol','ror','neg','inc','dec','imul','mul']:F=v
            if op in ['mul'] or (op=='imul' and len(args)==1):write('%rax',True);write('%rdx',True)
        else:
            emit(unknown,i,'unsupported instruction semantics');T.update(regs(','.join(args)));F=True
        succ=[]
        if op not in ['ret','int3']:
            if op.startswith('j'):
                m=re.match(r'([\da-f]+)',i['args']);t=hex(int(m[1],16)) if m else None
                if t in at:succ.append(at[t])
                elif op=='jmp':emit(unknown,i,'tail transfer/target not composed')
            if op!='jmp' and j+1<len(ins):succ.append(j+1)
        for k in succ:
            old=states.get(k)
            new=(T,M,F) if old is None else (T|old[0],M|old[1],F or old[2])
            if old!=new:states[k]=(set(new[0]),set(new[1]),new[2]);q.append(k)
    if host:unknown[('entry','host')]=dict(reason='aggregate witness/public ABI and indirect callees not reconstructed')
    return dict(seed=dict(secret_registers=sorted(initial),memory='non-stack/non-RIP loads secret',public='pointers, lengths, layout, pow exponent; conditional on caller provenance'),classification='UNRESOLVED' if alerts or unknown else 'CLEAN',alerts=list(alerts.values()),unresolved=list(unknown.values()),tainted_instruction_mnemonics=sorted(tainted_ops),states=len(states),fixpoint_steps=rounds)
rows=[]
for a,f in selected.items():
    row={k:v for k,v in f.items() if k!='instructions'};row['source_from_debug']=None;row['source_debug_reason']='ELF has no .debug_info/.debug_line; symbols do not enumerate inline instances';row['audit']=analyze(f);row['call_sites']=[e for e in edges if e['target']==hex(a)];rows.append(row)
inv={a for a,f in func.items() if any(re.search(r'::(?:try_inv|inv)$',n) for n in f['names'])}
invrows=[]
for a in sorted(inv):
    f=func[a];invrows.append(dict(address=hex(a),end=f['end'],names=f['names'],transfers=[e for e in edges if e['target']==hex(a)],classification='UNRESOLVED',reason='operand provenance/nonzero-or-charged-event theorem not composed; inline inversions cannot be enumerated without provenance'))
# All branch/indirect/latency candidates in the complete linked text, not just
# names that happened to survive inlining. This is a completeness backstop only.
candidates=[]
for a,f in func.items():
    for i in f['instructions']:
        if (i['op'].startswith('j') and i['op']!='jmp') or (i['op'] in ['call','jmp'] and i['args'].startswith('*')) or re.match(r'(?:i?div|v?divs[sd]|v?sqrts[sd]|bsf|bsr|pdep|pext|rdrand|rdseed)',i['op']):
            candidates.append(dict(function=hex(a),**i))
save('instances.json',rows);save('inversions.json',invrows);save('calls.json',edges);save('unresolved-indirect.json',unresolved)
with lzma.open(D/'whole-image-candidates.json.xz','wt') as out:json.dump(candidates,out)
with lzma.open(D/'function-index.json.xz','wt') as out:json.dump([{k:v for k,v in f.items() if k!='instructions'} for f in func.values()],out)
selected_asm='\n\n'.join('\n'.join([f"{f['address']} {f['names']}"]+[i['text'] for i in f['instructions']]) for f in selected.values())
(D/'selected-disassembly.txt').write_text(selected_asm+'\n')
# Preserve raw image disassembly compressed, hashed uncompressed.
(D/'disassembly.txt.sha256').write_text(hashlib.sha256(asm.encode()).hexdigest()+'\n')
with lzma.open(D/'disassembly.txt.xz','wt') as out:out.write(asm)
(D/'disassembly.txt').unlink()
summary=dict(binary=str(B),binary_sha256=hashlib.sha256(B.read_bytes()).hexdigest(),binary_bytes=B.stat().st_size,dwarf_present=bool(re.search(r'\.debug_(info|line)\s',sec)),functions=len(func),selected=len(rows),classifications=dict(collections.Counter(r['audit']['classification'] for r in rows)),resolved_transfers=len(edges),unresolved_indirect=len(unresolved),whole_image_review_candidates=len(candidates),inline_completeness=False,print_axioms='N/A: finite static machine-code audit, no Lean theorem')
save('summary.json',summary);print(json.dumps(summary))
