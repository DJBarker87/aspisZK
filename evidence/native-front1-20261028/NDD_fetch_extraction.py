from pathlib import Path
import subprocess,json
E=Path(__file__).resolve().parent
code="""from pathlib import Path
import json
b=Path('/home/dombarker/project-offloads/codex-cx-native-front1-20261028/NDD_extracted');print(json.dumps({str(p.relative_to(b)):p.read_text() for p in b.rglob('*.lean')}))"""
r=subprocess.run(['ssh','-o','ControlMaster=no','dombarker@100.108.41.90','python3'],input=code,text=True,capture_output=True);assert r.returncode==0,r.stderr
for n,s in json.loads(r.stdout).items():p=E/n;p.parent.mkdir(parents=True,exist_ok=True);p.write_text(s)
