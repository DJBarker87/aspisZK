from NKP_formal import *
import base64
for a,module,script in [('NKP_L025','NKP_TracePackagingFinal','NKP_package_final.py'),('NKP_L026','NKP_ExportFinal','NKP_export_final.py')]:
 rc=run(a,'cache',module,['python3',script],extra={script:(E/script).read_text()});assert rc['exit_status']==0
r=ssh('python3',f'''from pathlib import Path
import json,base64
b=Path({B!r});names=list(b.glob('NKP_NEP_*.xz'))+list(b.glob('NKP_NEP_*.sha256'))+[b/'NKP_PACKAGING_FINAL.json',b/'NKP_EXPORT_FINAL.json']
print(json.dumps({{p.name:base64.b64encode(p.read_bytes()).decode() for p in names}}))
''');assert r.returncode==0
for n,s in json.loads(r.stdout).items():(E/n).write_bytes(base64.b64decode(s))
print('FINAL_TRACES_AND_EXPORT_FETCHED')
