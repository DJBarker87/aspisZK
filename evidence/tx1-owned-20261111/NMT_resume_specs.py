from pathlib import Path
import json,hashlib,re
from NMT_formal import run
root=Path('evidence/rowspec-lead-20261107');e=Path(__file__).resolve().parent
names=[]
def visit(n):
 if n in names:return
 s=(root/(n+'.lean')).read_text()
 for dep in re.findall(r'^import (RSL_\w+)',s,re.M):visit(dep)
 names.append(n)
visit('RSL_TX1_345')
pins=[]
for i,n in enumerate(names,61):
 raw=(root/(n+'.lean')).read_bytes();s=raw.decode();s=re.sub(r'^import (RSL_\w+)',r'import NMT_\1',s,flags=re.M)
 # Canonical sources are copied verbatim except imports; rejection theorems are existing specs, not new roots.
 (e/('NMT_'+n+'.lean')).write_text(s)
 pins.append({'source':str(root/(n+'.lean')),'sha256':hashlib.sha256(raw).hexdigest(),'copy':'NMT_'+n+'.lean','changes':'import module names only'})
(e/'NMT_RSL_PROVENANCE.json').write_text(json.dumps(pins,indent=1)+'\n')
for i,n in enumerate(names,61):
 if (e/f'NMT_L{i:03}'/'receipt.json').exists():continue
 r=run(f'NMT_L{i:03}','lean','NMT_'+n)
 if r['exit_status']:raise SystemExit(1)
