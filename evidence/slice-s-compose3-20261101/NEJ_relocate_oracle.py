"""Remove only our initial empty module hook; per-target hooks are reversible."""
from pathlib import Path
import subprocess,json
E=Path(__file__).resolve().parent
p='crates/aspis-statement/src/pool_v1/mod.rs';frozen=subprocess.check_output(['git','show','4bb3b3f51e16b4525f1d10336e2b0bcbbd775387:'+p],text=True)
code=f'''from pathlib import Path
import json,hashlib,subprocess
b=Path('/home/dombarker/project-offloads/codex-cx-slice-s-compose3-20261029')
with (b/'NEJ_RELOCATE-barrier.log').open('w') as f:r=subprocess.run(['python3','/home/dombarker/project-offloads/codex-cx-s2h-20261023/S2H_reservation.py',str(b/'NEJ_RELOCATE-admission.json')],stdout=f,stderr=subprocess.STDOUT)
ad=json.loads((b/'NEJ_RELOCATE-admission.json').read_text());assert r.returncode==0 and ad['allowed'] is True
s=b/'NEJ_src';pins=json.loads((b/'NEJ_RUST_SHA256.json').read_text());assert all(hashlib.sha256((s/n).read_bytes()).hexdigest()==h for n,h in pins.items())
p=s/{p!r};old=p.read_text();assert old=={(frozen+chr(10)+'#[cfg(kani)]'+chr(10)+'mod NEJ_oracle;'+chr(10))!r};p.write_text({frozen!r});pins[{p!r}]=hashlib.sha256(p.read_bytes()).hexdigest();(b/'NEJ_RUST_SHA256.json').write_text(json.dumps(pins,indent=1))
print(json.dumps(dict(path={p!r},old_sha256=hashlib.sha256(old.encode()).hexdigest(),restored_frozen_sha256=pins[{p!r}],admission=ad)))
'''
r=subprocess.run(['ssh','-o','ControlMaster=no','dombarker@100.108.41.90','python3'],input=code,text=True,capture_output=True);assert r.returncode==0,r.stderr
(E/'NEJ_ORACLE_RELOCATION.json').write_text(r.stdout)
