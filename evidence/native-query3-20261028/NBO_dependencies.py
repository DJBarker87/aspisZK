from pathlib import Path
import json,subprocess,shlex
E=Path(__file__).resolve().parent;R=E.parents[1]
# Priority is repository owner source; only then accepted leaf packet source.
roots=[R/'lean',R/'docs/research/100bit-spend-path-20261013/lean',R/'evidence/leaf-p6-8-20261027',R/'evidence/replay-tops1-20261027',R/'docs/research/100bit-spend-path-20261013/lean-candidates/current-circle-wrapper-20261019']
sources={}
for root in roots:
 for p in root.rglob('*.lean'):
  if p.stem not in sources:sources[p.stem]=p
  key='.'.join(p.relative_to(root).with_suffix('').parts)
  if key not in sources:sources[key]=p
seen=set();graph={};pending=['FIo_MixedValues']
while pending:
 name=pending.pop()
 if name in seen:continue
 seen.add(name);p=sources.get(name) or sources.get(name.rsplit('.',1)[-1])
 if p is None:continue
 imports=[]
 for line in p.read_text().splitlines():
  if line.startswith('import '):imports+=line[7:].split()
 graph[name]=dict(source=str(p.relative_to(R)),imports=imports)
 pending+=imports
(E/'NBO_DEPENDENCY_GRAPH.json').write_text(json.dumps(graph,indent=2)+'\n')
# Read-only lookup against exactly the compiler's LEAN_PATH selection.
paths=['/home/dombarker/project-offloads/codex-cx-query-cache-20261028','/home/dombarker/project-offloads/codex-cx-sound-int2-20261025','/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects','/home/dombarker/.elan/toolchains/leanprover--lean4---v4.32.0/lib/lean']
code='from pathlib import Path;import json,hashlib;names='+repr(sorted(seen))+';roots='+repr(paths)+'''
out={}
for n in names:
 p=next((Path(r)/(n.replace('.','/')+'.olean') for r in roots if (Path(r)/(n.replace('.','/')+'.olean')).is_file()),None)
 out[n]=None if p is None else dict(path=str(p),sha256=hashlib.sha256(p.read_bytes()).hexdigest(),bytes=p.stat().st_size)
print(json.dumps(out))
'''
r=subprocess.run(['ssh','-o','ConnectTimeout=15','dombarker@100.108.41.90','python3 -c '+shlex.quote(code)],capture_output=True,text=True)
assert r.returncode==0,r.stderr
available=json.loads(r.stdout);(E/'NBO_DEPENDENCY_AVAILABLE.json').write_text(json.dumps(available,indent=2)+'\n')
order=[];done=set()
def visit(n):
 if n in done:return
 done.add(n)
 if n not in graph:
  assert available.get(n) is not None,'unavailable source '+n
  return
 for d in graph[n]['imports']:visit(d)
 if available.get(n) is None:order.append(n)
visit('FIo_MixedValues')
(E/'NBO_DEPENDENCY_PLAN.json').write_text(json.dumps([dict(module=n,source=graph[n]['source']) for n in order],indent=2)+'\n')
print(json.dumps(dict(missing=len(order),modules=order)))
