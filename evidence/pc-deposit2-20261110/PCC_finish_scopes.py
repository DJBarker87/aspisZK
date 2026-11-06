from PCC_formal import *
import base64,lzma
old=json.loads((E/'PCC_L001.json').read_text())['deps_fingerprint']['selected_objects']
files={'PCC_pin_closure.py':(E/'PCC_pin_closure.py').read_text(),'PCC_PREDECESSOR_PINS.json':json.dumps(old)}
r=run('PCC_L069','inspect','resolved closure and predecessor object pins',['python3','PCC_pin_closure.py','PCC_L069'],files);assert r['exit_status']==0
rr=ssh('python3',f'''from pathlib import Path
import json,base64
b=Path({B!r})/'PCC_closure';print(json.dumps({{p.name:base64.b64encode(p.read_bytes()).decode() for p in b.iterdir() if p.is_file()}}))
''');assert rr.returncode==0,rr.stderr
for n,data in json.loads(rr.stdout).items():(E/n).write_bytes(base64.b64decode(data))
files={n:(E/n).read_text() for n in ['PCC_retention.py','PCC_ROOT_MANIFEST.json']}
r=run('PCC_L070','inspect','support gate and input retention',['python3','PCC_retention.py','PCC_L070'],files);assert r['exit_status']==0
