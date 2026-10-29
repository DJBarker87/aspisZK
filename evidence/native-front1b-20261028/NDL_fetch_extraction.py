"""Read back an existing extraction; never starts or resubmits a job."""
from pathlib import Path
import subprocess,json,sys
E=Path(__file__).resolve().parent;namespace=sys.argv[1];assert namespace.startswith('NDL_')
code="""from pathlib import Path
import json
b=Path('/home/dombarker/project-offloads/codex-cx-native-front1b-20261028');d=b/(NS+'_extracted')
print(json.dumps({str(p.relative_to(d)):p.read_text() for p in d.rglob('*.lean')}))
""".replace('NS',repr(namespace))
r=subprocess.run(['ssh','-o','ControlMaster=no','-o','ConnectTimeout=15','dombarker@100.108.41.90','python3'],input=code,text=True,capture_output=True);assert r.returncode==0,r.stderr
out=json.loads(r.stdout);assert out
for n,s in out.items():
 p=E/n;assert p.is_relative_to(E);p.parent.mkdir(parents=True,exist_ok=True);p.write_text(s)
