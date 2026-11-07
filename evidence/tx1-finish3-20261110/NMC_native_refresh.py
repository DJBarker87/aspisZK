from NMC_patch_inputs import moduleText
from pathlib import Path
import json,hashlib,difflib
B=Path(__file__).resolve().parent;S=B/'NMC_src';pins=json.loads((B/'NMC_SOURCE_PINS.json').read_text())
for name,path in [('NMC_segments','crates/aspis-r1-cost-probe/src'),('NMC_program','programs/r1-cost-probe/src')]:
 p=S/path/(name+'.rs');before=p.read_text();after=moduleText(name);p.write_text(after)
 pins[str(p.relative_to(S))]=hashlib.sha256(p.read_bytes()).hexdigest()
 with (B/'NMC_NATIVE.patch').open('a') as f:f.write(''.join(difflib.unified_diff(before.splitlines(True),after.splitlines(True),fromfile='a/'+str(p.relative_to(S)),tofile='b/'+str(p.relative_to(S)))))
(B/'NMC_SOURCE_PINS.json').write_text(json.dumps(pins))
print('Borrowed parent replaces retired by-value native shape; no frozen body changed')
