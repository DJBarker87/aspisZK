from pathlib import Path
import json,hashlib,subprocess,difflib
E=Path(__file__).resolve().parent;F='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387'
from NGO_inputs import load
inputs=load();pins=json.loads((E/'NGO_SOURCE_PINS.json').read_text());patch=[]
for n,s in inputs.items():
 pins[n]=hashlib.sha256(s.encode()).hexdigest()
 r=subprocess.run(['git','show',F+':'+n],capture_output=True,text=True)
 old=r.stdout if r.returncode==0 else ''
 patch+=difflib.unified_diff(old.splitlines(True),s.splitlines(True),fromfile='a/'+n if old else '/dev/null',tofile='b/'+n)
(E/'NGO_SOURCE_PINS.json').write_text(json.dumps(pins,indent=1));(E/'NGO_harness.patch').write_text(''.join(patch))
