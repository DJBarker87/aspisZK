from pathlib import Path
import subprocess,json
E=Path(__file__).resolve().parent
records=json.loads((E/'NFO_HOST_PINS.json').read_text())['imports']
code="""from pathlib import Path
import json,hashlib,shutil
records=json.loads(RECORDS);out=[]
for r in records:
 if not r['source'].endswith('.olean'):continue
 for suffix in ['.private','.server']:
  src=Path(r['source']+suffix);dst=Path(r['destination']+suffix)
  if not src.exists():continue
  h=hashlib.sha256(src.read_bytes()).hexdigest()
  if dst.exists():assert hashlib.sha256(dst.read_bytes()).hexdigest()==h
  else:shutil.copy2(src,dst)
  out.append(dict(source=str(src),destination=str(dst),sha256=h))
print(json.dumps(out,indent=1))
""".replace('RECORDS',repr(json.dumps(records)))
r=subprocess.run(['ssh','-o','ControlMaster=no','dombarker@100.108.41.90','python3'],input=code,text=True,capture_output=True)
assert r.returncode==0,r.stderr
(E/'NFO_SIDECAR_PINS.json').write_text(r.stdout);print('Copied',len(json.loads(r.stdout)),'matching private/server companions')
