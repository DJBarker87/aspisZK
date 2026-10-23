#!/usr/bin/env python3
"""Independently cross-check frozen call decoding with LLVM's disassembler."""
import collections,hashlib,json,re,struct,subprocess
from pathlib import Path
H=Path('/home/dombarker/project-offloads/codex-cx-s10-repin2-20261023')
F=Path('/home/dombarker/project-offloads/codex-cx-s10-repin2-20261023')
LLVM=Path('/home/dombarker/.cache/solana/v1.52/platform-tools/llvm/bin')
sha=lambda b:hashlib.sha256(b).hexdigest()
old=json.loads((F/'collected/elf-graphs.json').read_text())
result={}
for mode,g in old['artifacts'].items():
    p=Path(g['linked']['path']);raw=p.read_bytes();assert sha(raw)==g['linked']['sha256']
    output=subprocess.check_output([str(LLVM/'llvm-objdump'),'-d',str(p)],text=True)
    relocs=subprocess.check_output([str(LLVM/'llvm-readelf'),'-r',str(p)],text=True)
    headers=subprocess.check_output([str(LLVM/'llvm-readelf'),'-S',str(p)],text=True)
    bysite={}
    for line in output.splitlines():
        m=re.match(r'\s*([0-9a-f]+):\s+(?:[0-9a-f]{2} ){7}[0-9a-f]{2}\s+\t(callx?|call)\s+(.+)',line)
        if not m:continue
        addr=int(m[1],16);op,arg=m[2],m[3];arg=arg.split()[0]
        bysite[addr]=dict(address=addr,op=op,operand=arg)
    original={c['address']:c for c in g['calls']}
    assert set(original)==set(bysite),(mode,len(original),len(bysite))
    calls=[]
    for addr,c in sorted(original.items()):
        asm=bysite[addr]
        if c['kind']=='direct':
            target=addr+8+8*int(asm['operand'],0)
            assert asm['op']=='call' and target==c['target']
            asm.update(kind='direct',caller=c['caller'],target=target,status='ELF confirmed')
        elif c['kind']=='indirect':
            assert asm['op']=='callx' and asm['operand']=='r'+str(c['immediate'])
            asm.update(kind='indirect',caller=c['caller'],status='target unresolved; instruction confirmed')
        elif c['kind']=='syscall':
            assert asm['op']=='call'
            relocation=next(l for l in relocs.splitlines() if l.strip().startswith(f'{addr:016x} '))
            assert c['target'] in relocation
            asm.update(kind='syscall',caller=c['caller'],target=c['target'],relocation=relocation.strip(),status='ELF relocation confirmed')
        else:raise AssertionError(c)
        calls.append(asm)
    # Independently retain relocated code pointers. These are candidates, not
    # an inferred callx target without a path-sensitive pointer-flow argument.
    h=struct.unpack_from('<16sHHIQQQIHHHHHH',raw)
    sections=[struct.unpack_from('<IIQQQQIIQQ',raw,h[6]+i*h[11]) for i in range(h[12])]
    functions={s['address'] for s in g['symbols'] if s['size']}
    pointers=[]
    for line in relocs.splitlines():
        m=re.match(r'([0-9a-f]{16})\s+\S+\s+R_SBF_64_RELATIVE',line.strip())
        if not m:continue
        address=int(m[1],16)
        section=next(s for s in sections if s[3]<=address<s[3]+s[5] and s[1]!=8)
        pos=section[4]+address-section[3]
        if section[2]&4: # lddw: 32-bit immediate halves in two instructions
            value=struct.unpack_from('<I',raw,pos+4)[0] | struct.unpack_from('<I',raw,pos+12)[0]<<32
        else:value=struct.unpack_from('<Q',raw,pos)[0]
        if value in functions:pointers.append(dict(location=address,target=value,executable_section=bool(section[2]&4)))
    names=collections.defaultdict(list)
    for s in g['symbols']:names[s['address']].append(s['name'])
    result[mode]=dict(linked=g['linked'],deployed=g['deployed'],text_sha256=g['text_sha256'],
        objdump_sha256=sha(output.encode()),objdump_bytes=len(output.encode()),
        relocation_dump_sha256=sha(relocs.encode()),relocation_dump_bytes=len(relocs.encode()),
        debug_info_present='.debug_info' in headers,calls=calls,address_taken_functions=pointers,
        indirect_sites=[dict(**c,caller_symbols=names[c['caller']],
            reason='Runtime register/vtable target requires source pointer-flow or accepted-path exclusion; address-taken set is not proof of a target')
            for c in calls if c['kind']=='indirect'])
out=dict(schema='s10-llvm-independent-call-check-v1',tools={str(LLVM/x):sha((LLVM/x).read_bytes()) for x in ['llvm-objdump','llvm-readelf']},artifacts=result,
         scope='Frozen ELF instructions and relocations, including direct entrypoint lower bound. No DWARF inline map; no invented indirect edges.')
(H/'elf-crosscheck.json').write_text(json.dumps(out,indent=2,sort_keys=True)+'\n')
print(json.dumps({k:dict(calls=len(v['calls']),indirect=len(v['indirect_sites']),pointers=len(v['address_taken_functions'])) for k,v in result.items()}))
