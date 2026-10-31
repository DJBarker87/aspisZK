from NEF_host import *
from NEF_FNPTR_SPECIALISATION import build,inputs
import hashlib
admit('NEF_SPECIALISE001')
src,nodes=inputs();out,_,_=build(src,nodes)
files={n:s for n,s in out.items() if s!=src[n]}
files['crates/aspis-r1-cost-probe/src/NEF_native.rs']=(E/'NEF_marker_harness.rs.txt').read_text()+'\n'+(E/'NEF_static_ref.rs.txt').read_text()
r=py(f'''from pathlib import Path
import json,hashlib
b=Path({B!r})/'NEF_src';files=json.loads({json.dumps(files)!r})
for n,t in files.items():(b/n).write_text(t)
print(json.dumps({{n:hashlib.sha256((b/n).read_bytes()).hexdigest() for n in files}}))
''');assert r.returncode==0,r.stderr
pins=json.loads((E/'NEF_SCRATCH_PINS.json').read_text());pins.update(json.loads(r.stdout));(E/'NEF_SCRATCH_PINS.json').write_text(json.dumps(pins,indent=2)+'\n')
