"""Update own scratch harness inputs, with pinned before hashes and admission.
No shared source, cache, launcher, shim or reservation implementation is edited.
"""
from pathlib import Path
import subprocess,json,hashlib,sys
E=Path(__file__).resolve().parent;B='/home/dombarker/project-offloads/codex-cx-native-prepare4-20261028'
assert not (E/'NCA_ACTIVE.json').exists()
label=sys.argv[1];updates={}
for pair in sys.argv[2:]:
    relative,local=pair.split('=',1)
    assert relative in ['crates/aspis-r1-cost-probe/src/NCA_wire.rs','crates/aspis-r1-cost-probe/src/r1_wire.rs']
    updates[relative]=Path(local).read_text()
x=dict(B=B,label=label,updates=updates,pins=json.loads((E/'NCA_SOURCE.json').read_text()))
code=r'''from pathlib import Path
import json,subprocess,hashlib
x=json.loads(PAYLOAD);b=Path(x['B']);s=b/'NCA_src';label=x['label']
with (b/(label+'-barrier.log')).open('w') as f:
 r=subprocess.run(['python3','/home/dombarker/project-offloads/codex-cx-s2h-20261023/S2H_reservation.py',str(b/(label+'-reservation.json'))],stdout=f,stderr=subprocess.STDOUT)
a=json.loads((b/(label+'-reservation.json')).read_text());assert r.returncode==0 and a['allowed'] is True,(r.returncode,a)
for n,text in x['updates'].items():
 p=s/n;assert not p.is_symlink();assert hashlib.sha256(p.read_bytes()).hexdigest()==x['pins']['source_sha256'][n];p.write_text(text);x['pins']['source_sha256'][n]=hashlib.sha256(p.read_bytes()).hexdigest()
print(json.dumps(dict(source=x['pins'],reservation=a)))
'''.replace('PAYLOAD',repr(json.dumps(x)))
r=subprocess.run(['ssh','-o','ConnectTimeout=15','dombarker@100.108.41.90','python3'],input=code,capture_output=True,text=True)
(E/(label+'-setup.log')).write_text(r.stdout+r.stderr);assert r.returncode==0,r.stderr
v=json.loads(r.stdout);(E/'NCA_SOURCE.json').write_text(json.dumps(v['source'],indent=2)+'\n');(E/(label+'-reservation.json')).write_text(json.dumps(v['reservation'],indent=2)+'\n')
