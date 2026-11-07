from NMT_formal import *
import base64
function=sys.argv[1];a={'tx1':'NMT_E001','first':'NMT_E002','stage1_owned':'NMT_E003'}[function]
# Payload upload occurs only after recorded admission, before the serial launch.
admission(a+'_upload')
files=['NMT_stage.py','NMT_OPACITY.json','NMT_STAGING_MANIFEST.json','NMT_FROZEN_PAYLOAD.json.sha256','NMT_FROZEN_PAYLOAD.json.xz']
r=ssh('python3',f'''from pathlib import Path
import json,base64
b=Path({B!r});data=json.loads({json.dumps({n:base64.b64encode((E/n).read_bytes()).decode() for n in files})!r})
for n,s in data.items():(b/n).write_bytes(base64.b64decode(s))
''');assert r.returncode==0,r.stderr
r=run(a,'extract',function,['python3','NMT_stage.py','--extract','--function',function,'--workspace',B+'/NMT_src','--out',B+'/NMT_extracted/'+function,'--opacity',B+'/NMT_OPACITY.json'])
r2=ssh('python3',f'''from pathlib import Path
import json,base64
b=Path({B!r});p=b/'NMT_extracted'/{function!r}
print(json.dumps({{str(q.relative_to(b)):base64.b64encode(q.read_bytes()).decode() for q in p.rglob('*') if q.is_file()}}))
''');assert r2.returncode==0,r2.stderr
for n,s in json.loads(r2.stdout).items():
 raw=base64.b64decode(s);p=E/n;p.parent.mkdir(parents=True,exist_ok=True)
 if len(raw)>20*1024*1024:p.with_name(p.name+'.xz').write_bytes(lzma.compress(raw));p.with_name(p.name+'.sha256').write_text(sha(raw)+'\n')
 else:p.write_bytes(raw)
print('EXTRACTION',function,r['exit_status'],flush=True)
