from pathlib import Path
import json,hashlib,difflib,lzma,base64,re
B=Path(__file__).resolve().parent;S=B/'NKA_src';n='crates/aspis-r1-cost-probe/src/r1_semantic.rs';p=S/n;pins=json.loads((B/'NKA_SOURCE_PINS.json').read_text());assert hashlib.sha256(p.read_bytes()).hexdigest()==pins[n]
body=(B/'NKA_write_event.rs.txt').read_text();original=p.read_text();assert 'out.as_mut_ptr()' in original
# Native stage has the exact original write with its decode reply explicit;
# only a fresh ghost Bool assignment follows the completed typed write.
assert 'unsafe{out.as_mut_ptr().cast::<Row>().add(p).write(reply?);}' in body
p.write_text(original+'\n'+body);pins[n]=hashlib.sha256(p.read_bytes()).hexdigest();(B/'NKA_SOURCE_PINS.json').write_text(json.dumps(pins,indent=2))
payload=json.loads(lzma.decompress((B/'NKA_FROZEN_PAYLOAD.json.xz').read_bytes()));patch=''
for name in sorted(pins):
 if name not in payload:continue
 old=base64.b64decode(payload[name]).decode();patch+=''.join(difflib.unified_diff(old.splitlines(True),(S/name).read_text().splitlines(True),fromfile='a/'+name,tofile='b/'+name))
(B/'NKA_NATIVE.patch').write_text(patch)
(B/'NKA_WRITE_EVENT_SITE.json').write_text(json.dumps(dict(source=n,source_sha256=pins[n],harness_sha256=hashlib.sha256(body.encode()).hexdigest(),ghost='fresh local Bool, set only AFTER typed ptr::write completes',erasure='delete written parameter and assignment; replace explicit reply with SAME decoder result',no_allocation=True,cargo_target_dir=str(B/'NKA_target')),indent=2))
print('NKA typed-write event cut installed separately from allocation and data windows')
