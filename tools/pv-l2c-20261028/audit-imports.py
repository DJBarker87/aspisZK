"""Static postmortem including public imports; not a replacement compiler replay."""
from pathlib import Path
import json,re,ast
R=Path(__file__).resolve().parents[2];E=R/'evidence/pv-l2c-20261028'
# Reuse only the comment stripper without executing the source resolver.
tree=ast.parse((R/'tools/pv-l2c-20261028/resolve.py').read_text());node=next(x for x in tree.body if isinstance(x,ast.FunctionDef) and x.name=='uncomment');ns={};exec(compile(ast.Module(body=[node],type_ignores=[]),'comment-stripper','exec'),ns)
def imports(s):
 out=[]
 for line in ns['uncomment'](s).splitlines():
  m=re.match(r'^\s*(?:(?:public|private)\s+)?import\s+(.+)$',line)
  if m:out.extend(re.findall(r'[A-Za-z_][A-Za-z_0-9]*(?:\.[A-Za-z_][A-Za-z_0-9]*)*',m[1]))
 return out
sources=json.load(open(E/'focused-project-sources.json'));original=dict(sources)
for p in (R/'docs/research/v8-r0-zk-20261009/lean').glob('PV_L2C_*.lean'):sources[p.stem]=p.read_text()
ext={x['module'].replace('/','.') for x in json.load(open(R/'evidence/pv-runjoin20-20261027/external-object-manifest.json'))}
results={}
for root in sorted(x for x in sources if x.startswith('PV_L2C_')):
 seen=set();missing=set();todo=[root]
 while todo:
  m=todo.pop()
  if m in seen or m in ext:continue
  seen.add(m)
  if m not in sources:missing.add(m);continue
  todo.extend(imports(sources[m]))
 results[root]=dict(missing_from_recorded_resolution=sorted(missing),project_nodes=len(seen))
edges=[]
for m,b in original.items():
 old=re.findall(r'^import\s+(\S+)',ns['uncomment'](b),re.M)
 for dep in imports(b):
  if dep not in old:edges.append(dict(module=m,previously_omitted_import=dep))
(E/'public-import-postmortem.json').write_text(json.dumps(dict(classification='static postmortem only; no compile replay or closure credit',omitted_edges=edges,roots=results),indent=2)+'\n')
print('Omitted edges:',edges)
print('Accepted local roots with missing dependencies:',{m:x['missing_from_recorded_resolution'] for m,x in results.items() if x['missing_from_recorded_resolution'] and m!='PV_L2C_FocusedReplay'})
