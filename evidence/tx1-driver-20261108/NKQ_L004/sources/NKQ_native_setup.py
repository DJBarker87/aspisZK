from pathlib import Path
import json,hashlib,subprocess
import NKQ_stage as stage
B=Path(__file__).resolve().parent;S=B/'NKQ_src';O=B/'NKQ_preflight';O.mkdir(exist_ok=True)
stage.stage(S);stage.validate(S,O,'/home/dombarker/.cargo/bin/cargo')
r=subprocess.run(['git','apply',str(B/'NKQ_KMX.patch')],cwd=S,capture_output=True,text=True);assert r.returncode==0,r.stderr
pins={n:hashlib.sha256((S/n).read_bytes()).hexdigest() for n in ['KMX_stubs.rs','KMX_native.rs','KMX_CopyMeaning.lean']}
frozen={n:v['sha256'] for n,v in json.loads((B/'NKQ_STAGING_MANIFEST.json').read_text())['files'].items() if n not in pins}
(B/'NKQ_SOURCE_PINS.json').write_text(json.dumps(pins,indent=2));(B/'NKQ_FROZEN_FILE_PINS.json').write_text(json.dumps(frozen,indent=2))
print('Frozen corpus staged; KMX exact patch applied; frozen graph checked')
