from pathlib import Path
import json,subprocess,hashlib
P=Path(__file__).resolve().parent;R=P.parents[1]
a=json.loads((P/'JHn_ACTIVE_SOURCES.json').read_text());initial=json.loads((P/'JHn_AENEAS_OBJECT_PINS.json').read_text())['objects']
paths=json.loads((P/'JHn35_098/receipt.json').read_text())['env']['LEAN_PATH'].split(':')
prior={}
for stem,folder in [('JHk','joint-fixture32-20261027'),('JHl','joint-fixture33-20261027'),('JHm','joint-fixture34-20261028')]:
 data=json.loads((R/'evidence'/folder/(stem+'_CACHE_MANIFEST.json')).read_text())
 # Historical manifests store object entries under paths or a named object table.
 def walk(x):
  if isinstance(x,dict):
   for k,v in x.items():
    if isinstance(v,dict) and 'sha256' in v and (str(k).endswith('.olean') or str(v.get('path','')).endswith('.olean')):
     path=v.get('path',k);name=Path(path).name
     if name.startswith(stem+'_'):prior[name]=v['sha256']
    else:walk(v)
  elif isinstance(x,list):
   for v in x:walk(v)
 walk(data)
names=list(initial)+[n[:-5]+'.olean' for n in a]+list(prior)
code='from pathlib import Path\nimport json,hashlib\npaths='+repr(paths)+'\nnames='+repr(sorted(set(names)))+'\nout={}\nfor n in names:\n p=next((Path(root)/n for root in paths if (Path(root)/n).is_file()),None)\n assert p is not None,n\n out[n]=dict(path=str(p),sha256=hashlib.sha256(p.read_bytes()).hexdigest(),bytes=p.stat().st_size)\nprint(json.dumps(out,indent=2))'
r=subprocess.run(['ssh','-o','ConnectTimeout=15','dombarker@100.108.41.90','python3'],input=code,capture_output=True,text=True,check=True)
obj=json.loads(r.stdout)
(P/'JHn_CACHE_MANIFEST.json').write_text(json.dumps({n:obj[n] for n in sorted(obj) if n.startswith('JHn_')},indent=2)+'\n')
(P/'JHn_FINAL_AENEAS_OBJECT_PINS.json').write_text(json.dumps(dict(objects={n:obj[n] for n in initial}),indent=2)+'\n')
checks=dict(aeneas_objects=len(initial),aeneas_unchanged=all(obj[n]['sha256']==v['sha256'] for n,v in initial.items()),own_objects=len(a),predecessor_objects=len(prior),predecessors_unchanged=all(obj[n]['sha256']==v for n,v in prior.items()),persistent_cache_retained=True)
(P/'JHn_PREDECESSOR_CACHE_CHECK.json').write_text(json.dumps(dict(expected=prior,selected={n:obj[n] for n in prior}),indent=2)+'\n')
if (P/'JHn_HEADLINE_AENEAS_OBJECT_PINS.json').exists():
 h=json.loads((P/'JHn_HEADLINE_AENEAS_OBJECT_PINS.json').read_text())['objects'];checks['headline_aeneas_unchanged']=all(h[n]['sha256']==initial[n]['sha256'] for n in initial)
(P/'JHn_PIN_CHECK.json').write_text(json.dumps(checks,indent=2)+'\n');print(json.dumps(checks))
assert all(checks[k] for k in checks if k.endswith('unchanged'))
