from pathlib import Path
import json,lzma,subprocess,hashlib
D=Path(__file__).resolve().parent; B=D.parent/'pv-mfb-20261029'
tr=json.load(lzma.open(B/'exact-traces.json.xz')); f=json.load(open(B/'dlib-preflight-input.json'))
mods={}
for id in ['V228','V243','V211']:
 for m,v in next(r for r in tr if r['id']==id)['modules'].items():
  if not (m.startswith('PV_B3P_') or m in {'R1Z.PV_CB_Op105Types','R1Z.PV_CB_Op105Funs','R1Z.PV_CB_Op105Exact'}):continue
  b=subprocess.check_output(['git','show','HEAD:'+v['path']]);assert hashlib.sha256(b).hexdigest()==v['sha256']
  mods[m]=dict(v); p=D/'sources'/(m.replace('.','/')+'.lean');p.parent.mkdir(exist_ok=True,parents=True);p.write_bytes(b)
# ExternalTypes/ExternalFuns are taken from the fully fingerprinted dlib cohort.
(D/'rebuild-input.json').write_text(json.dumps(dict(modules=mods,rows={r['id']:r['closing'] for r in tr if r['id'] in ['V228','V243','V211']},source_revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),base_revision='b0ceae89f9'),indent=2)+'\n')
print(len(mods))
