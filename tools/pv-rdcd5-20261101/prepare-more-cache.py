from pathlib import Path
import json,subprocess,hashlib
R=Path(__file__).resolve().parents[2];E=R/'evidence/pv-rdcd5-20261101';p=json.load(open(E/'source-resolution.json'));f=json.load(open(E/'dlib-resume-fingerprint.json'));rs=json.load(open(E/'dlib-receipts-index.json'));out={}
for m,a in p['modules'].items():
 key=m.replace('.','/');o=f['project'].get(key);s=f['source_closure'].get(key)
 if not o or not s:continue
 matches=[r for r in rs if r.get('module')==key and r['exit']==0 and r.get('source_sha256')==a['sha256']]
 if not matches:continue
 rec=matches[-1];out[key]=dict(authority=a,recorded=rec,object_record=o,source_record=s)
(E/'more-cache-records.json').write_text(json.dumps(out,indent=2)+'\n');print('Additional complete candidate records:',len(out))
