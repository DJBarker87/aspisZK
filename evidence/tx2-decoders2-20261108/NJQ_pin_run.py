from NJQ_formal import *
import base64
rc=run('NJQ_L074','pin','NJQ_pin',['python3','NJQ_pin.py'],{'NJQ_pin.py':(E/'NJQ_pin.py').read_text()});assert rc['exit_status']==0
r=ssh('python3',f'''from pathlib import Path
import json,base64
b=Path({B!r});names=['NJQ_CLOSURE_PINS.json.xz','NJQ_CLOSURE_PINS.json.sha256','NJQ_PREDECESSOR_COMPARISON.json','NJQ_EXPORT.json']
print(json.dumps({{n:base64.b64encode((b/n).read_bytes()).decode()for n in names}}))
''');assert r.returncode==0
for n,t in json.loads(r.stdout).items():(E/n).write_bytes(base64.b64decode(t))
print('Retained checked own export and selected closure pins.',flush=True)
