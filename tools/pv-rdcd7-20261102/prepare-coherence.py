"""Freeze current sources, accepted launches and retained source bindings."""
from pathlib import Path
import json,subprocess,hashlib
R=Path(__file__).resolve().parents[2];E=R/'evidence/pv-rdcd7-20261102'
plan=json.load(open(E/'source-resolution.json'));modules={m.replace('.','/'):x for m,x in plan['modules'].items() if plan['module_kinds'][m]=='ordinary-focused'}
for m,x in modules.items():assert hashlib.sha256((R/x['path']).read_bytes()).hexdigest()==x['sha256'],m
launches={}
for p in E.glob('lean-*/receipt.json'):
 j=json.load(open(p))
 if j['exit']!=0:continue
 if j['module'] not in modules:continue
 assert j['source_sha256']==modules[j['module']]['sha256'],j['module']
 d=E/j['dependencies_snapshot'];assert hashlib.sha256(d.read_bytes()).hexdigest()==j['dependencies_sha256']
 launches[str(j['attempt'])]=dict(receipt=j,dependencies=json.load(open(d)))
extra=[]
for name in ['v197-library-sources.json','library-sources.json']:
 for x in json.load(open(R/'evidence/pv-rdcd4-20261029'/name)):
  extra.append(dict(path=x['path'],sha256=x['sha256']))
(E/'coherence-inputs.json').write_text(json.dumps(dict(revision=subprocess.check_output(['git','rev-parse','HEAD'],cwd=R,text=True).strip(),modules=modules,launches=launches,native_source_pins=extra),indent=2)+'\n')
print(len(modules),'project source pins;',len(launches),'accepted launches;',len(extra),'native source pins')
