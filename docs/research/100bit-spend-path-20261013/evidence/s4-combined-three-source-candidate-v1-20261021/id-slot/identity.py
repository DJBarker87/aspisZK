#!/usr/bin/env python3
"""Audit same-source SBF ELFs. Run on the host, with artifacts retained there."""
import hashlib, json, struct, subprocess, sys
from pathlib import Path
h=Path(sys.argv[1]); out=h/'receipts/identity'; out.mkdir()
llvm=Path('/home/dombarker/.cache/solana/v1.52/platform-tools/llvm/bin')
def sections(b):
 e=struct.unpack_from('<16sHHIQQQIHHHHHH',b)
 raw=[struct.unpack_from('<IIQQQQIIQQ',b,e[6]+i*e[11]) for i in range(e[12])]
 names=raw[e[13]]; names=b[names[4]:names[4]+names[5]]
 return {names[s[0]:].split(b'\0',1)[0].decode():dict(offset=s[4],size=s[5],address=s[3]) for s in raw}
def decode(s):
 n=0
 for c in s:n=n*58+'123456789ABCDEFGHJKLMNPQRSTUVWXYZabcdefghijkmnopqrstuvwxyz'.index(c)
 return n.to_bytes(32,'big')
paths={m:h/'artifacts'/m/'aspis_r1_cost_probe_program.so' for m in ['default','devnet']}
b={m:p.read_bytes() for m,p in paths.items()}; sec={m:sections(x) for m,x in b.items()}
assert sec['default']==sec['devnet']
for m,p in paths.items():
 (out/f'{m}.sections.txt').write_bytes(subprocess.check_output([str(llvm/'llvm-objdump'),'-h',str(p)]))
 t=sec[m]['.text'];(out/f'{m}.text').write_bytes(b[m][t['offset']:t['offset']+t['size']])
with (out/'cmp.txt').open('w') as f:
 r=subprocess.run(['cmp',str(out/'default.text'),str(out/'devnet.text')],stdout=f,stderr=f)
 f.write(f'cmp .text exit={r.returncode}\n')
assert r.returncode==0
slots=[]; patched=bytearray(b['default']); template=json.loads((h/'r1-devnet.template.json').read_text())
for kind,v in [('pool',0x41),('registry',0x44)]:
 needle=bytes([v])*32; pos=b['default'].find(needle)
 assert pos>=0 and b['default'].find(needle,pos+1)<0
 name,s=next((n,s) for n,s in sec['default'].items() if s['offset']<=pos and pos+32<=s['offset']+s['size'])
 assert name=='.rodata'
 expected=decode(template['programs'][kind]);assert b['devnet'][pos:pos+32]==expected
 patched[pos:pos+32]=expected
 slots.append(dict(id=kind,section=name,file_offset=pos,section_offset=pos-s['offset'],bytes=32,devnet_base58=template['programs'][kind],devnet_hex=expected.hex()))
assert bytes(patched)==b['devnet'], 'difference outside deployment slots'
diffs=[i for i,(x,y) in enumerate(zip(b['default'],b['devnet'])) if x!=y]
report=dict(source_revision='731018bdc',text_identical=True,only_two_data_slots=True,differing_bytes=len(diffs),slots=slots,artifacts={m:dict(sha256=hashlib.sha256(x).hexdigest(),bytes=len(x),sections=sec[m]) for m,x in b.items()})
(out/'identity.json').write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(report,indent=2))
