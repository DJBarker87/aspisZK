"""Read retained predecessor evidence only; never launch native work."""
from pathlib import Path
import json,subprocess,hashlib
E=Path(__file__).resolve().parent;P=E.parent/'pc-helpers1-20261110';D=E/'PCE_PREDECESSOR_NATIVE';D.mkdir(exist_ok=True)
ns=['PCB_K111','PCB_K112','PCB_K113','PCB_K114','PCB_K115','PCB_K116','PCB_K117','PCB_K118','PCB_K119']
want=[n+s for n in ns for s in ['-graph-check.json','-lock-check.json','-selected-features.txt']]
code="from pathlib import Path\nimport json\nb=Path('/home/dombarker/project-offloads/codex-pc-helpers1-20261110')\nnames="+repr(want)+"\nprint(json.dumps({n:(b/n).read_text() if (b/n).is_file() else None for n in names}))\n"
r=subprocess.run(['ssh','-o','ControlMaster=no','-o','ConnectTimeout=15','dombarker@100.108.41.90','python3'],input=code,capture_output=True,text=True);assert r.returncode==0,r.stderr
x=json.loads(r.stdout);missing=[];pins=[]
for n,s in x.items():
 if s is None:missing.append(n);continue
 (D/n).write_text(s);pins.append(dict(name=n,sha256=hashlib.sha256(s.encode()).hexdigest(),provenance='READ-ONLY retained PCB host receipt; no native resubmission',committed_predecessor_missing=True))
(E/'PCE_RECOVERED_INPUTS.json').write_text(json.dumps(dict(files=pins,missing=missing),indent=1)+'\n')
assert not missing,missing
print('Recovered '+str(len(pins))+' retained candidate native sidecars read-only; zero native runs.')
