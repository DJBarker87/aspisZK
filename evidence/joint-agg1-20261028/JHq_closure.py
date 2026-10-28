"""Read-only recursive import and historical object-hash preflight."""
from pathlib import Path
import json,re,subprocess,shlex
E=Path(__file__).resolve().parent;R=E.parents[1];seen=set()
def visit(n):
 if n in seen:return
 seen.add(n);p=R/'lean'/(n.replace('.','/')+'.lean')
 if p.exists():
  for m in re.findall(r'^import\s+(\S+)',p.read_text(),re.M):visit(m)
for n in ['JHn_TX1Frontier','JHn_ExactReturned','JHn_Joint']:visit(n)
names=sorted(n for n in seen if n.startswith(('JHn_','JHe_')))
pins={}
def add(row,source):
 name=Path(row['path']).name
 if name.startswith(('JHn_','JHe_')):pins.setdefault(name,{}).setdefault(row['sha256'],[]).append(source)
for f in (R/'evidence').glob('joint-fixture*/**/receipt.json'):
 try:x=json.loads(f.read_text())
 except (ValueError,OSError):continue
 for row in x.get('deps_fingerprint',{}).get('selected_objects',{}).values():add(row,str(f.relative_to(R)))
f=R/'evidence/joint-fixture30-20261027/JHe_CACHE_CLEANUP.json'
def walk(x):
 if isinstance(x,dict):
  if 'path' in x and 'sha256' in x:add(x,str(f.relative_to(R)))
  else:
   for v in x.values():walk(v)
 elif isinstance(x,list):
  for v in x:walk(v)
walk(json.loads(f.read_text()))
manifest=json.loads((R/'evidence/joint-fixture35-20261028/JHn_CACHE_MANIFEST.json').read_text())
for name,row in manifest.items():pins[name]={row['sha256']:['evidence/joint-fixture35-20261028/JHn_CACHE_MANIFEST.json']}
missing=[n for n in names if n+'.olean' not in pins];print('required',len(names),'without recorded pin',missing,flush=True);assert not missing
paths=json.loads((R/'evidence/joint-fixture35-20261028/JHn35_092/receipt.json').read_text())['env']['LEAN_PATH'].split(':')
x=dict(names=names,paths=paths,pins=pins)
code='''import json,hashlib,sys
from pathlib import Path
x=json.loads(sys.stdin.read());rows=[]
for n in x['names']:
 key=n.replace('.','/')+'.olean';p=next((Path(root)/key for root in x['paths'] if (Path(root)/key).is_file()),None)
 h=hashlib.sha256(p.read_bytes()).hexdigest() if p else None
 rows.append(dict(module=n,path=str(p),sha256=h,matched=h in x['pins'][key],pin_sources=x['pins'][key].get(h,[])))
print(json.dumps(dict(method='recursive source import closure for both TX1 imports and Joint; first match in unchanged lane LEAN_PATH checked against historical consumer or manifest SHA256',objects=rows,all_matched=all(r['matched'] for r in rows)),indent=2))
'''
r=subprocess.run(['ssh','-o','ConnectTimeout=15','dombarker@100.108.41.90','python3 -c '+shlex.quote(code)],input=json.dumps(x),capture_output=True,text=True)
assert r.returncode==0,r.stderr
(E/'JHq_CLOSURE_PREFLIGHT.json').write_text(r.stdout);out=json.loads(r.stdout);print('all matched',out['all_matched']);print([r for r in out['objects'] if not r['matched']]);assert out['all_matched']
