#!/usr/bin/env python3
"""Supplement frozen linked text census with raw ELF symbol kinds/aliases."""
import hashlib,json,struct
from pathlib import Path
H=Path('/home/dombarker/project-offloads/codex-cx-s10-inventory-20261021')
F=Path('/home/dombarker/project-offloads/codex-cx-pin-20261020')
sha=lambda b:hashlib.sha256(b).hexdigest()
result={}
for mode in ['default','devnet','pool']:
 p=F/'artifacts'/mode/'linked.elf';raw=p.read_bytes();h=struct.unpack_from('<16sHHIQQQIHHHHHH',raw)
 sections=[struct.unpack_from('<IIQQQQIIQQ',raw,h[6]+i*h[11]) for i in range(h[12])]
 rows=[]
 for s in sections:
  if s[1]!=2:continue
  st=sections[s[6]];strings=raw[st[4]:st[4]+st[5]]
  for off in range(s[4],s[4]+s[5],s[9]):
   n,info,other,idx,value,size=struct.unpack_from('<IBBHQQ',raw,off)
   if idx==0 or idx>=len(sections) or not (sections[idx][2]&4):continue
   name=strings[n:strings.index(b'\0',n)].decode()
   rows.append(dict(raw_name=name,address=value,size=size,kind=info&15,binding=info>>4,section=idx,visibility=other))
 result[mode]=dict(linked_sha256=sha(raw),symbols=rows)
(H/'collected/elf-symbol-kinds.json').write_text(json.dumps(dict(schema='s10-raw-elf-symbol-kinds-v1',artifacts=result),indent=2,sort_keys=True)+'\n')
print({m:len(x['symbols']) for m,x in result.items()})
