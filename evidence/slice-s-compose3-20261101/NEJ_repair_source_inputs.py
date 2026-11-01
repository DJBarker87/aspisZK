"""Fill omitted unchanged frozen include files; never alter a checked byte."""
from pathlib import Path
import subprocess,json,hashlib
E=Path(__file__).resolve().parent;rev='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387'
r=subprocess.run(['ssh','-o','ControlMaster=no','dombarker@100.108.41.90','python3'],input="from pathlib import Path\nimport json\np=Path('/home/dombarker/project-offloads');a=p/'codex-cx-slice-s-compose2-20261029/NEE_src';b=p/'codex-cx-slice-s-compose3-20261029/NEJ_src';print(json.dumps([str(f.relative_to(a)) for f in a.rglob('*') if f.is_file() and not (b/f.relative_to(a)).exists()]))",text=True,capture_output=True)
assert r.returncode==0,r.stderr
available=set(subprocess.check_output(['git','ls-tree','-r','--name-only',rev],text=True).splitlines())
paths=[p for p in json.loads(r.stdout) if p in available and p.endswith(('.rs','.toml','.json'))]
files={p:subprocess.check_output(['git','show',rev+':'+p],text=True) for p in paths}
code='''from pathlib import Path
import subprocess,json,hashlib,sys
b=Path('/home/dombarker/project-offloads/codex-cx-slice-s-compose3-20261029')
with (b/'NEJ_INPUT_REPAIR2-barrier.log').open('w') as f:r=subprocess.run(['python3','/home/dombarker/project-offloads/codex-cx-s2h-20261023/S2H_reservation.py',str(b/'NEJ_INPUT_REPAIR2-admission.json')],stdout=f,stderr=subprocess.STDOUT)
ad=json.loads((b/'NEJ_INPUT_REPAIR2-admission.json').read_text());assert r.returncode==0 and ad['allowed'] is True
s=b/'NEJ_src';pins=json.loads((b/'NEJ_RUST_SHA256.json').read_text());assert all(hashlib.sha256((s/n).read_bytes()).hexdigest()==h for n,h in pins.items())
files=FILES
for n,v in files.items():
 p=s/n;assert not p.exists() or p.read_text()==v
 p.parent.mkdir(parents=True,exist_ok=True);p.write_text(v);pins[n]=hashlib.sha256(p.read_bytes()).hexdigest()
(b/'NEJ_RUST_SHA256.json').write_text(json.dumps(pins,indent=1))
print(json.dumps(dict(frozen_revision=REV,files={n:hashlib.sha256(v.encode()).hexdigest() for n,v in files.items()},reason='K001 frozen include files absent from inherited path manifest',admission=ad)))
'''.replace('FILES',repr(files)).replace('REV',repr(rev))
r=subprocess.run(['ssh','-o','ControlMaster=no','dombarker@100.108.41.90','python3'],input=code,text=True,capture_output=True);assert r.returncode==0,r.stderr
(E/'NEJ_INPUT_REPAIR2.json').write_text(r.stdout)
