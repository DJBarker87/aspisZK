import json,subprocess,hashlib
from pathlib import Path
D=Path(__file__).resolve().parent
f=json.load(open(D/'dlib-fingerprint.json'));errors=[]
for m,v in f['source_closure'].items():
 if v.get('external'):continue
 p=v['source_path'];b=subprocess.check_output(['git','show','HEAD:'+p]);v['head_sha256']=hashlib.sha256(b).hexdigest();v['head_blob']=subprocess.check_output(['git','rev-parse','HEAD:'+p],text=True).strip()
 if v['head_sha256']!=v['source_sha256']:errors.append(m)
f['current_revision']=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip();f['source_mismatches']=errors
(D/'dlib-preflight-input.json').write_text(json.dumps(f,indent=2))
print('Current source mismatches',errors)
