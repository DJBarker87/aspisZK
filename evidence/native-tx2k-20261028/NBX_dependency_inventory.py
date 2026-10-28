from pathlib import Path
import subprocess,json,re,hashlib
E=Path(__file__).resolve().parent
code='''from pathlib import Path
import json
roots=[Path('/home/dombarker/project-offloads/codex-cx-tx2codec-cache-20261028'),Path('/home/dombarker/project-offloads/codex-cx-sound-int2-20261025'),Path('/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects'),Path('/home/dombarker/.elan/toolchains/leanprover--lean4---v4.32.0/lib/lean')]
x={}
for r in roots:
 paths=r.glob('*.olean') if r.name=='codex-cx-sound-int2-20261025' else r.rglob('*.olean')
 for p in paths:x.setdefault(str(p.relative_to(r).with_suffix('')).replace('/','.'),str(p))
print(json.dumps(x))
'''
r=subprocess.run(['ssh','-o','ConnectTimeout=15','dombarker@100.108.41.90','python3 -c '+__import__('shlex').quote(code)],capture_output=True,text=True);assert r.returncode==0,r.stderr
objects=json.loads(r.stdout)
sources={p.stem:p for d in ['docs/research/100bit-spend-path-20261013/lean','lean'] for p in Path(d).glob('*.lean')}
seen=set();missing=[];unknown=[]
def visit(n):
 if n in seen:return
 seen.add(n)
 if n not in sources:
  if n not in objects:unknown.append(n)
  return
 p=sources[n]
 for x in re.findall(r'^import (\S+)',p.read_text(),re.M):visit(x)
 if n not in objects:missing.append(dict(module=n,path=str(p),sha256=hashlib.sha256(p.read_bytes()).hexdigest()))
import sys
root=sys.argv[1] if len(sys.argv)>1 else 'IDa_Deployed'
visit(root)
x=dict(root=root,available_objects=len(objects),closure_modules=len(seen),missing=missing,unknown=unknown)
(E/('NBX_DEPENDENCY_'+root+'.json')).write_text(json.dumps(x,indent=2)+'\n');print(json.dumps(x,indent=2))
