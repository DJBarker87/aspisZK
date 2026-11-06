from pathlib import Path
import json,hashlib,lzma,base64,difflib
B=Path(__file__).resolve().parent;S=B/'NKA_src';pins=json.loads((B/'NKA_SOURCE_PINS.json').read_text());n='crates/aspis-core/src/r0/heap.rs';p=S/n;assert hashlib.sha256(p.read_bytes()).hexdigest()==pins[n]
s=p.read_text();assert 'fn rejection_control(){check(2);}' in s;s=s.replace('fn rejection_control(){check(2);}','fn rejection_control(){rejection_mapper_check(true);}')
a=s.index('#[cfg(kani)] mod NKA_heap_effects');end=s.index('#[cfg(kani)] mod NKA_reserve_continuation',a);close=s.rfind('}',a,end);s=s[:close]+(B/'NKA_reserve_error.rs.txt').read_text()+s[close:];p.write_text(s);pins[n]=hashlib.sha256(p.read_bytes()).hexdigest();(B/'NKA_SOURCE_PINS.json').write_text(json.dumps(pins,indent=2))
payload=json.loads(lzma.decompress((B/'NKA_FROZEN_PAYLOAD.json.xz').read_bytes()));patch=''
for name in sorted(pins):
 if name not in payload:continue
 old=base64.b64decode(payload[name]).decode();patch+=''.join(difflib.unified_diff(old.splitlines(True),(S/name).read_text().splitlines(True),fromfile='a/'+name,tofile='b/'+name))
(B/'NKA_NATIVE.patch').write_text(patch)
print('NKA original rejection_control repaired with actual std reserve-error frames and mapper; no Global OOM claim')
