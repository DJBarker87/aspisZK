from NJN_formal import *
r=run('NJN_L029','inspect','NJN_export',['python3','NJN_export_host.py'],{'NJN_export_host.py':(E/'NJN_export_host.py').read_text()});assert r['exit_status']==0
rr=ssh('python3',f'''from pathlib import Path
import json,base64
b=Path({B!r});names=['NJN_EXPORT.json','NJN_CLOSURE_PINS.json.xz','NJN_CLOSURE_PINS.json.sha256'];print(json.dumps({{n:base64.b64encode((b/n).read_bytes()).decode() for n in names}}))
''');assert rr.returncode==0
import base64
for n,s in json.loads(rr.stdout).items():(E/n).write_bytes(base64.b64decode(s))
