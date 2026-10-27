"""Rebind only the certificate dependency cone, preserving consumer declarations."""
from pathlib import Path
import re,json,sys,hashlib
R=Path(__file__).resolve().parents[2];P=Path(__file__).resolve().parent
src=json.loads((P/'JGy_SOURCE_CLOSURES.json').read_text()); groups=json.loads((P/'JGy_GROUPS.json').read_text())
certs={m:g['module'] for g in groups for m in g['originals']}
tainted=set(certs)
while True:
 n=tainted|{m for m,v in src.items() if any(d in tainted for d in v['imports'])}
 if n==tainted:break
 tainted=n
layouts={f'JGr_M{i}Layout' for i in range(3)};tainted|=layouts
orders=[];parts=[]
for i in range(3):
 root=f'JGw_Tree{i}';seen=set();order=[]
 def visit(m):
  if m in seen:return
  seen.add(m)
  for d in src.get(m,{}).get('imports',[]):visit(d)
  if m in tainted and m not in certs:order.append(m)
 visit(root)
 layers=[[],[],[],[],[],[],[],[]]
 for m in order:
  if m==f'JGr_M{i}Layout' or m==f'JGr_M{i}Leaves':k=0
  elif m==f'JGr_M{i}BranchLo':k=1
  elif m in [f'JGr_M{i}BranchHi',f'JGr_M{i}Root']:k=2
  elif re.fullmatch(r'JGu_Level'+str(i)+r'_\d\d',m):k=4+int(m[-2:])//6
  elif m in [f'JGu_Initial{i}',f'JGu_Levels{i}',f'JGu_Terminal{i}',f'JGw_Terminal{i}',f'JGw_Tree{i}']:k=7
  else:k=3
  layers[k].append(m)
 for k,ms in enumerate(layers):
  if ms:parts.append((f'JGy_Tree{i}Part{k}',ms))
modmap={**certs,**{m:mod for mod,ms in parts for m in ms}}
# Identify namespace roots exported by the replaced modules, including multi-namespace files.
nsmap={}
for m in tainted:
 s=(R/'lean'/f'{m}.lean').read_text()
 for ns in re.findall(r'namespace AspisR1\.([A-Za-z0-9_]+)',s):
  if ns.startswith('JGr_'):nsmap[ns]=ns.replace('JGr_','JGy_Gr_',1)
  elif ns.startswith('JGu_'):nsmap[ns]=ns.replace('JGu_','JGy_Gu_',1)
  elif ns.startswith('JGw_'):nsmap[ns]=ns.replace('JGw_','JGy_Gw_',1)
light=json.loads((P/'JGy_LIGHT.json').read_text())
nsmap.update(light['namespaces']);modmap.update(light['module_map'])
pat=re.compile(r'\b('+'|'.join(sorted(map(re.escape,nsmap),key=len,reverse=True))+r')\b')
def rename(s):return pat.sub(lambda m:nsmap[m[0]],s)
manifest=[]
for mod,ms in parts:
 imports=[];bodies=[];original=[]
 for m in ms:
  f=R/'lean'/f'{m}.lean';s=f.read_text()
  for d in src[m]['imports']:
   if d in light['removed_unused_imports']:continue
   d=modmap.get(d,d)
   if d!=mod and d not in imports:imports.append(d)
  body='\n'.join(l for l in s.splitlines() if not l.startswith('import '))+'\n'
  for unused in light['removed_unused_irreducible_attributes']:body=body.replace(' '+unused,'')
  bodies.append(rename(body));original.append(dict(module=m,sha256=hashlib.sha256(f.read_bytes()).hexdigest()))
 text=''.join('import '+d+'\n' for d in imports)+'\n'.join(bodies)
 f=R/'lean'/f'{mod}.lean'
 if '--check' in sys.argv:assert f.read_text()==text
 else:f.write_text(text)
 manifest.append(dict(module=mod,originals=original,imports=imports,source_sha256=hashlib.sha256(text.encode()).hexdigest()))
(P/'JGy_CONSUMERS.json').write_text(json.dumps(manifest,indent=2)+'\n')
(P/'JGy_NAMESPACE_MAP.json').write_text(json.dumps(nsmap,indent=2)+'\n')
# Assert all grouped imports form an acyclic graph before any host build.
completed=set(certs.values())|{'JGy_LightCore','JGy_LightPadding'}
for row in manifest:
 for dependency in row['imports']:
  if dependency.startswith('JGy_'):assert dependency in completed,(row['module'],dependency)
 completed.add(row['module'])
print('Consumer modules',len(manifest),'legacy sources',sum(len(ms) for _,ms in parts))
for row in manifest:print(row['module'],','.join(x['module'] for x in row['originals']))
