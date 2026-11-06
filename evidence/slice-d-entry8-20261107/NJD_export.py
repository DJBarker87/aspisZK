from NJD_formal import *
r=run('NJD_L031','inspect','NJD_export',['python3','NJD_export_host.py'],{'NJD_export_host.py':(E/'NJD_export_host.py').read_text()});assert r['exit_status']==0
rr=ssh('python3',f'''from pathlib import Path
import json,base64
b=Path({B!r});names=['NJD_EXPORT.json','NJD_CLOSURE_PINS.json.xz','NJD_CLOSURE_PINS.json.sha256'];print(json.dumps({{n:base64.b64encode((b/n).read_bytes()).decode() for n in names}}))
''');assert rr.returncode==0
import base64
for n,s in json.loads(rr.stdout).items():(E/n).write_bytes(base64.b64decode(s))
