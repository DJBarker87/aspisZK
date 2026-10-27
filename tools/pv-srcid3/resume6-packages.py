#!/usr/bin/env python3
"""Read-only recursive inventory of the effective Lean package import closure."""
import pathlib,json,subprocess
root=pathlib.Path(__file__).resolve().parents[2];e=root/'evidence/pv-srcid3-20261026'
d=json.loads((e/'resume6-full-closure.json').read_text())
# The remote script is metadata-only; it launches no Lean/Rust process.
code=r'''
import pathlib,json,re,hashlib
h=pathlib.Path('/home/dombarker/project-offloads');j=h/'aspis-joint-20261019'
env=json.loads((h/'r1-privacy-build-integration-20261019/env/J.json').read_text())
roots=[str(j/'objects')]+env['LEAN_PATH'].split(':')
source_roots=[str(j/'sources')]
for r in roots:
 if '/.lake/build/lib/lean' in r:source_roots.append(r.split('/.lake/build/lib/lean')[0])
source_roots += [env['LEAN_SYSROOT']+'/src/lean',env['LEAN_SYSROOT']+'/src/lean/lake']
known={r['module']:r for r in EXPECTED}
seen={};todo=[r['module'] for r in EXPECTED if r['module'].startswith('R1Z.PV_Src_')]
def imports(s):
 # Remove nested Lean comments and strings before reading import lines.
 out=[];i=0;depth=0;string=False
 while i<len(s):
  c=s[i];p=s[i:i+2]
  if depth:
   if p=='/-':depth+=1;i+=2;continue
   if p=='-/':depth-=1;i+=2;continue
   out.append('\n' if c=='\n' else ' ');i+=1;continue
  if string:
   if c=='\\':i+=2;continue
   if c=='"':string=False
   out.append('\n' if c=='\n' else ' ');i+=1;continue
  if p=='/-':depth=1;i+=2;continue
  if p=='--':
   n=s.find('\n',i);i=len(s) if n<0 else n;continue
  if c=='"':string=True;out.append(' ');i+=1;continue
  out.append(c);i+=1
 cleaned=''.join(out);a=[]
 for line in cleaned.splitlines():
  m=re.match(r'^\s*(?:(?:public|private|meta)\s+)*import\s+(.+)',line)
  if m:a.extend(x for x in m.group(1).split() if x not in {'all'})
 if not re.search(r'^\s*prelude\s*$',cleaned,re.M):a.append('Init')
 return sorted(set(a))
while todo:
 m=todo.pop()
 if m in seen:continue
 rel=m.replace('.','/');obj=next((pathlib.Path(r)/(rel+'.olean') for r in roots if (pathlib.Path(r)/(rel+'.olean')).is_file()),None)
 src=next((pathlib.Path(r)/(rel+'.lean') for r in source_roots if (pathlib.Path(r)/(rel+'.lean')).is_file()),None)
 row={'module':m,'object_path':str(obj) if obj else None,'object_sha256':hashlib.sha256(obj.read_bytes()).hexdigest() if obj else None,'host_source_path':str(src) if src else None,'host_source_sha256':hashlib.sha256(src.read_bytes()).hexdigest() if src else None}
 if src:deps=imports(src.read_text())
 elif m in known:deps=known[m]['imports'];row['import_graph_gap']='host source unavailable; expected research/branch imports used'
 else:deps=[];row['import_graph_gap']='host source unavailable; nested closure cannot be enumerated'
 row['imports']=deps;seen[m]=row;todo.extend(deps)
print(json.dumps({'objects':list(seen.values()),'source_roots':source_roots,'object_roots':roots}))
'''.replace('EXPECTED',repr(d['project_modules']))
r=subprocess.run(['ssh','dombarker@100.108.41.90','python3 -'],input=code,text=True,capture_output=True,check=True)
(e/'resume6-package-closure.json').write_text(r.stdout+'\n');out=json.loads(r.stdout)
print('objects',len(out['objects']),'missing objects',sum(not r['object_path'] for r in out['objects']),'missing sources',sum(not r['host_source_path'] for r in out['objects']))
