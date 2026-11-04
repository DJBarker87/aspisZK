from NFB_remote import *
import lzma,hashlib
assert not (E/'NFB_ACTIVE.json').exists()
a='NFB_COPY_CONFIG_INPUT';admit(a)
x=json.loads(lzma.decompress((E/'NFB_K002_INPUTS.json.xz').read_bytes()))
keys=['NFB_src/crates/aspis-r1-cost-probe/src/verifier/NFB_geometry.rs','NFB_SOURCE_PINS.json']
upload(a,{k:x[k] for k in keys})
(E/'NFB_SOURCE_PINS.json').write_text(x['NFB_SOURCE_PINS.json'])
r=ssh(a,'python3',f'''from pathlib import Path
import json
b=Path({B!r});files=[]
for p in (b/'NFB_tmp').rglob('*'):
 if p.is_file() and (p.name.startswith('external-sat') or p.name.startswith('smt2_dec_problem')):
  files.append(dict(path=str(p),bytes=p.stat().st_size));p.unlink()
print(json.dumps(files))
''');assert r.returncode==0;(E/'NFB_K012_TEMP_CLEANUP.json').write_text(r.stdout)
