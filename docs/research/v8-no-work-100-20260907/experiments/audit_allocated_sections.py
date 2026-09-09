#!/usr/bin/env python3
"""Read-only allocated-section census for the pinned research SBF ELFs."""
import hashlib,json,struct,sys
from pathlib import Path
def inspect(path):
    data=Path(path).read_bytes()
    assert data[:6]==b'\x7fELF\x02\x01','need little-endian ELF64'
    h=struct.unpack_from('<16sHHIQQQIHHHHHH',data)
    shoff,shsize,count,strindex=h[6],h[11],h[12],h[13]
    assert shsize==64 and 0<strindex<count and shoff+count*64<=len(data)
    sections=[struct.unpack_from('<IIQQQQIIQQ',data,shoff+i*64) for i in range(count)]
    st=sections[strindex];names=data[st[4]:st[4]+st[5]]
    out={}
    for s in sections:
        name=names[s[0]:].split(b'\0',1)[0].decode()
        if s[2]&2 and s[1]!=8:
            assert s[4]+s[5]<=len(data)
            out[name]={'bytes':s[5],'sha256':hashlib.sha256(data[s[4]:s[4]+s[5]]).hexdigest()}
    return {'elf_sha256':hashlib.sha256(data).hexdigest(),'elf_bytes':len(data),'allocated_sections':out}
assert len(sys.argv)==3
a,b=map(inspect,sys.argv[1:])
print(json.dumps({'reference':a,'candidate':b,'identical_allocated_sections':a['allocated_sections']==b['allocated_sections']},indent=2))
