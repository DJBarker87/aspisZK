"""Own sequential final support stages, after the one full raw replay."""
from NMB_formal import *
import base64

def support(a,script,extra=None):
 files={script:(E/script).read_text()};files.update(extra or {})
 r=run(a,'inspect',script,command=['python3',script],extra=files)
 if r['exit_status']:raise RuntimeError('Final support failure '+a)

def fetch(names):
 r=ssh('python3',f'''from pathlib import Path
import json,base64
b=Path({B!r});print(json.dumps({{n:base64.b64encode((b/n).read_bytes()).decode()for n in {names!r}}}))
''');assert r.returncode==0
 for n,s in json.loads(r.stdout).items():(E/n).write_bytes(base64.b64decode(s))

if __name__=='__main__':
 # L012 was never submitted earlier. IDs are unique; append order is actual chronology.
 support('NMB_L012','NMB_tools.py');fetch(['NMB_TOOLS.json'])
 support('NMB_L136','NMB_closure.py');fetch(['NMB_CLOSURE_PINS.json.xz','NMB_CLOSURE_PINS.json.sha256','NMB_CLOSURE_SUMMARY.json'])
 support('NMB_L137','NMB_export.py',{'NMB_AUDIT_PLAN.json':(E/'NMB_AUDIT_PLAN.json').read_text()});fetch(['NMB_EXPORT.json'])
 support('NMB_L138','NMB_retention.py',{'NMB_seed_inventory.json':lzma.decompress((E/'NMB_CACHE_IMPORTS.json.xz').read_bytes()).decode()});fetch(['NMB_RETENTION.json'])
 support('NMB_L139','NMB_aggregate.py');fetch(['NMB_AUDIT.json'])
 admissions={}
 for p in E.glob('NMB_[LK][0-9][0-9][0-9]-admission.json'):
  x=json.loads(p.read_text());assert x['exit']==0 and x['reservation']['allowed']is True;admissions[p.name]=x
 support('NMB_L140','NMB_finalcheck.py',{'NMB_admissions_snapshot.json':json.dumps(admissions)});fetch(['NMB_FINAL_CHECK.json'])
