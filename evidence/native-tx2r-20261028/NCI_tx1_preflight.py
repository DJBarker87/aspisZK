from pathlib import Path
import subprocess,json,hashlib
E=Path(__file__).resolve().parent
manifest=json.loads((E.parent/'sound-int2-20261025/object-source-manifest.json').read_text())
available=set(manifest['modules'])
cache=json.loads((E/'NCI_CACHE_START.json').read_text())
root='/home/dombarker/project-offloads/codex-cx-tx2resume-cache-20261028/'
for p in cache:
 if p.endswith('.olean'):available.add(p.removeprefix(root).removesuffix('.olean').replace('/','.'))
# The retained canonical source check identifies the additional coherent roots.
p=E.parent/'sound-int2-20261025/canonical-source-check.json'
if p.exists():
 d=json.loads(p.read_text())
 def walk(x):
  if isinstance(x,dict):
   for k,v in x.items():
    if k=='module' and isinstance(v,str):available.add(v)
    walk(v)
  elif isinstance(x,list):
   for v in x:walk(v)
 walk(d)
files=subprocess.check_output(['git','ls-tree','-r','--name-only','HEAD','lean','docs/research/100bit-spend-path-20261013/lean'],text=True).splitlines()
mapping={}
for p in sorted(files,key=lambda p:p.startswith('lean/')):
 if p.endswith('.lean'):
  prefix='lean/' if p.startswith('lean/') else 'docs/research/100bit-spend-path-20261013/lean/'
  mapping[p.removeprefix(prefix).removesuffix('.lean').replace('/','.')]=p
refined=(E/'NCI_END.json').exists()
if refined:available.update(json.loads((E/'NCI_END.json').read_text())['tx1']['available'])
missing=[];unknown=[];seen=set()
def visit(n):
 if n in seen or n in available:return
 seen.add(n)
 if n not in mapping:unknown.append(n);return
 p=mapping[n];s=subprocess.check_output(['git','show','HEAD:'+p],text=True)
 imports=[x for line in s.splitlines() if line.startswith('import ') for x in line[7:].split()]
 for x in imports:visit(x)
 missing.append(dict(module=n,path=p,source_sha256=hashlib.sha256(s.encode()).hexdigest(),imports=imports))
visit('JHq_TX1')
(E/('NCI_TX1_CLOSURE_PREFLIGHT.json' if refined else 'NCI_TX1_PREFLIGHT.json')).write_text(json.dumps(dict(scope='read-only local retained cache-name preflight; not host exhaustive object search or a compile',available_names=len(available),missing_count=len(missing),unknown=unknown,missing=missing),indent=2)+'\n')
print(json.dumps({'missing':len(missing),'unknown':unknown[:10]}))
