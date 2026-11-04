"""Retain latest successful own objects by copying into the lane-owned cache."""
from NFG_remote import *
import hashlib
from NFG_dependency_check import check_imports
assert not (E/'NFG_ACTIVE.json').exists()
rows=[json.loads(p.read_text()) for p in sorted(E.glob('NFG_L*/receipt.json'))];latest={r['module']:r for r in rows};generated=json.loads((E/'NFG_GENERATED.json').read_text());selected=[]
for m,r in latest.items():
 assert r['exit_status']==0,(m,'latest object is failed')
 assert not any('sorryAx' in s or '_native.decide.ax_' in s for s in r['print_axioms']),(m,'axiom')
 rel=m.replace('.','/')+'.lean';sf=E/(generated[m]['path'] if m in generated else rel)
 assert hashlib.sha256(sf.read_bytes()).hexdigest()==r['source_hashes'][rel]
 check_imports(sf,E,generated,rows)
 a=json.loads((E/r['attempt']/'object.json').read_text());a['source_text']=sf.read_text();selected.append(a)
admit('NFG_EXPORT')
code=f'''from pathlib import Path
import json,hashlib,shutil
b=Path({B!r});cache=Path('/home/dombarker/project-offloads/codex-cx-slice-q-compose6-cache-20261104/NFG_exports_20261104');cache.mkdir(parents=True,exist_ok=True)
out=[]
for r in json.loads({json.dumps(selected)!r}):
 p=Path(r['path']);assert hashlib.sha256(p.read_bytes()).hexdigest()==r['sha256']
 rel=r['module'].replace('.','/');q=cache/(rel+'.olean');q.parent.mkdir(parents=True,exist_ok=True);shutil.copy2(p,q)
 src=cache/(rel+'.lean');src.write_text(r.pop('source_text'));assert hashlib.sha256(src.read_bytes()).hexdigest()==r['source_sha256']
 companions=[]
 for suffix in ['.olean.private','.olean.server','.ir','.ilean']:
  extra=b/(rel+suffix)
  if extra.is_file():
   dest=cache/(rel+suffix);shutil.copy2(extra,dest);companions.append(dict(path=str(dest),sha256=hashlib.sha256(dest.read_bytes()).hexdigest()))
 r.update(export_path=str(q),export_sha256=hashlib.sha256(q.read_bytes()).hexdigest(),companions=companions);out.append(r)
print(json.dumps(dict(cache=str(cache),objects=out,policy='COPIED; own cache/workspace retained; no keys created or deleted'),indent=1))
'''
r=ssh('NFG_EXPORT','python3',code);assert r.returncode==0,r.stderr
(E/'NFG_OBJECT_EXPORTS.json').write_text(r.stdout)
print(json.dumps(dict(objects=len(selected),cache='/home/dombarker/project-offloads/codex-cx-slice-q-compose6-cache-20261104/NFG_exports_20261104')))
