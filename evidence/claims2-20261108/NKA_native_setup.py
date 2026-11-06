from pathlib import Path
import json,shutil,hashlib,subprocess
import NKA_stage as stage
B=Path(__file__).resolve().parent;P=Path('/home/dombarker/project-offloads/codex-cx-verify-observed7-20261108')
for n,h in json.loads((B/'NKA_PAYLOAD_PINS.json').read_text()).items():
 p=P/n;assert hashlib.sha256(p.read_bytes()).hexdigest()==h
 shutil.copyfile(p,B/n.replace('NJM_','NKA_'))
S=B/'NKA_src';(B/'NKA_preflight').mkdir(exist_ok=True)
stage.stage(S);stage.validate(S,B/'NKA_preflight','/home/dombarker/.cargo/bin/cargo')
r=subprocess.run(['git','apply',str(B/'NKA_KMX.patch')],cwd=S,capture_output=True,text=True);assert r.returncode==0,r.stderr
pins={}
for n in ['KMX_stubs.rs','KMX_native.rs','KMX_CopyMeaning.lean']:
 pins[n]=hashlib.sha256((S/n).read_bytes()).hexdigest()
manifest=json.loads((B/'NKA_STAGING_MANIFEST.json').read_text())
frozen={n:v['sha256'] for n,v in manifest['files'].items() if n not in pins}
(B/'NKA_SOURCE_PINS.json').write_text(json.dumps(pins,indent=2))
(B/'NKA_FROZEN_FILE_PINS.json').write_text(json.dumps(frozen,indent=2))
print('NKA frozen scratch and exact KMX staged')
