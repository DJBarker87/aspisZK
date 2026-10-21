#!/usr/bin/env python3
"""Compare all loaded bytes and relocations before transferring debug locations."""
import hashlib,json,struct,subprocess,os
from pathlib import Path
H=Path('/home/dombarker/project-offloads/codex-cx-s10-inventory5-20261021');F=H.parent/'codex-cx-pin-20261020'
version=os.environ.get('S10_DEBUG_VERSION','1')
L=Path('/home/dombarker/.cache/solana/v1.52/platform-tools/llvm/bin')
sha=lambda b:hashlib.sha256(b).hexdigest()
def sections(p):
    b=p.read_bytes();h=struct.unpack_from('<16sHHIQQQIHHHHHH',b);ss=[struct.unpack_from('<IIQQQQIIQQ',b,h[6]+i*h[11]) for i in range(h[12])];strings=ss[h[13]];names=b[strings[4]:strings[4]+strings[5]];out={}
    for s in ss:
        name=names[s[0]:].split(b'\0',1)[0].decode()
        raw=b[s[4]:s[4]+s[5]] if s[1]!=8 else b''
        out[name]=dict(type=s[1],flags=s[2],address=s[3],size=s[5],alignment=s[8],entry_size=s[9],sha256=sha(raw))
    return out
results=[]
for mode,version in [(m,v) for v in ['1','2'] for m in ['default','devnet','pool']]:
    name='aspis_pool.so' if mode=='pool' else 'aspis_r1_cost_probe_program.so';d=H/('build-'+mode+'-v'+version);p=d/'artifacts'/name
    if not p.exists():continue
    unstripped=d/('unstripped-'+name)
    pin=F/'artifacts'/mode/name;orig=sections(pin);debug=sections(p)
    required={n for n,s in orig.items() if s['flags']&2 or s['type'] in (4,9)}|{n for n,s in debug.items() if s['flags']&2 or s['type'] in (4,9)}
    comparisons=[dict(section=n,frozen=orig.get(n),debug=debug.get(n),equal=orig.get(n)==debug.get(n)) for n in sorted(required)]
    equal=all(c['equal'] for c in comparisons)
    r=dict(mode=mode,version=version,allocated_sections_and_relocations_identical=equal,sections=comparisons,
        frozen=dict(path=str(pin),sha256=sha(pin.read_bytes()),bytes=pin.stat().st_size),diagnostic=dict(path=str(p),sha256=sha(p.read_bytes()),bytes=p.stat().st_size),
        debug_sections=[n for n in sections(unstripped) if n.startswith('.debug')] if unstripped.exists() else [],
        trust='Debug locations transfer only if every allocated section and relocation section has identical bytes, virtual address, size, type, flags, alignment and entry width. This does not prove Rust/Lean semantics.')
    if equal and unstripped.exists() and r['debug_sections']:
        unsections=sections(unstripped)
        assert all(unsections[n]==debug[n] for n in required),'unstripped allocated bytes differ'
        # Disassemble DWARF only after the transfer preflight succeeds.
        output=subprocess.check_output([str(L/'llvm-dwarfdump'),'--debug-info','--debug-ranges',str(unstripped)])
        path=d/'debug-info.txt';path.write_bytes(output);r['dwarf']=dict(path=str(path),sha256=sha(output),bytes=len(output),generator='tools/s10-inventory5-20261021/debug-compare-host.py')
    results.append(r)
p=H/'debug-comparisons.json';p.write_text(json.dumps(dict(schema='s10-pass5-debug-transfer-v1',results=results),indent=2,sort_keys=True)+'\n')
print(json.dumps([dict(mode=r['mode'],transfer=r['allocated_sections_and_relocations_identical'],differences=[s['section'] for s in r['sections'] if not s['equal']],debug=r['debug_sections']) for r in results]))
