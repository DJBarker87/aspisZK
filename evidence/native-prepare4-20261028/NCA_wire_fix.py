from pathlib import Path
import subprocess,json,hashlib,shlex
E=Path(__file__).resolve().parent
B='/home/dombarker/project-offloads/codex-cx-native-prepare4-20261028'
part=(E/'NCA_COPY_CFG_PARENT.patch').read_text().split('+++ b/crates/aspis-r1-cost-probe/src/NCA_wire.rs\n',1)[1]
wire='\n'.join(line[1:] for line in part.splitlines()[1:] if line.startswith('+'))+'\n'
x=dict(B=B,wire=wire,pins=json.loads((E/'NCA_SOURCE.json').read_text()))
code=r"""from pathlib import Path
import json,subprocess,hashlib
x=json.loads(PAYLOAD);b=Path(x['B']);s=b/'NCA_src'
with (b/'NCA_WIRE_FIX-barrier.log').open('w') as f:
 r=subprocess.run(['python3','/home/dombarker/project-offloads/codex-cx-s2h-20261023/S2H_reservation.py',str(b/'NCA_WIRE_FIX-reservation.json')],stdout=f,stderr=subprocess.STDOUT)
a=json.loads((b/'NCA_WIRE_FIX-reservation.json').read_text());assert r.returncode==0 and a['allowed'] is True,(r.returncode,a)
p=s/'crates/aspis-r1-cost-probe/src/r1_wire.rs';assert hashlib.sha256(p.read_bytes()).hexdigest()==x['pins']['source_sha256'][str(p.relative_to(s))];text=p.read_text();assert '#[path="NCA_wire.rs"]' not in text;p.write_text(text.replace('pub(crate) mod NCA_wire;','#[path="NCA_wire.rs"]\npub(crate) mod NCA_wire;'))
x['pins']['source_sha256'][str(p.relative_to(s))]=hashlib.sha256(p.read_bytes()).hexdigest()
print(json.dumps(dict(source=x['pins'],reservation=a)))
""".replace('PAYLOAD',repr(json.dumps(x)))
r=subprocess.run(['ssh','-o','ConnectTimeout=15','dombarker@100.108.41.90','python3'],input=code,capture_output=True,text=True)
(E/'NCA_WIRE_FIX.log').write_text(r.stdout+r.stderr);assert r.returncode==0,r.stderr
v=json.loads(r.stdout);(E/'NCA_SOURCE.json').write_text(json.dumps(v['source'],indent=2)+'\n');(E/'NCA_WIRE_FIX.json').write_text(json.dumps(v['reservation'],indent=2)+'\n')
