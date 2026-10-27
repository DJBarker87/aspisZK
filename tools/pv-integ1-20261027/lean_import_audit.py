"""Read-only audit of op223's actual import closure; never installs a source."""
from pathlib import Path
import subprocess,json,hashlib,re
E=Path('evidence/pv-integ1-20261027');H='dombarker@100.108.41.90'
d=json.loads(Path('evidence/envj-rebuild-20261026/EJR_final-inventory.json').read_text());mapping={}
for row in d['selected']:
 if isinstance(row,dict) and row.get('resolution') and row.get('workspace')=='joint':mapping[row['module'].replace('/','.')]=row['resolution']
d2=json.loads(Path('evidence/envj-rebuild2-20261026/EJS_frontier-inventory.json').read_text())
for row in d2['ready']:mapping.setdefault(row['module'].replace('/','.'),{k:row[k] for k in ['path','revision','blob']})
code=r'''
from pathlib import Path
import json,re,hashlib
B=Path('/home/dombarker/project-offloads');D=B/'codex-pv-op223-20261027';J=B/'aspis-joint-20261019'
env=json.loads((D/'env-J.json').read_text());dirs=[D/'lean-objects',J/'objects']+[Path(p) for p in env['LEAN_PATH'].split(':')]
todo=['R1Z.PV_Op223_Source','R1Z.PV_Op223_V164'];rows={}
while todo:
 m=todo.pop()
 if m in rows:continue
 rel=m.replace('.','/')
 src=next((p for p in [D/'lean-sources'/(rel+'.lean'),J/'sources'/(rel+'.lean')] if p.exists()),None)
 obj=next((p for base in dirs if (p:=base/(rel+'.olean')).exists()),None)
 row=dict(module=m,source=str(src) if src else None,object=str(obj) if obj else None,object_sha256=hashlib.sha256(obj.read_bytes()).hexdigest() if obj else None)
 if src:
  text=src.read_text();row.update(source_sha256=hashlib.sha256(src.read_bytes()).hexdigest(),imports=re.findall(r'^import\s+(\S+)',text,re.M),private=str(src).startswith(str(D)))
  todo+=row['imports']
 rows[m]=row
print(json.dumps(rows))
'''
r=subprocess.run(['ssh',H,'python3','-'],input=code,text=True,capture_output=True,check=True);rows=json.loads(r.stdout)
changed=[];unresolved=[];dirty=[]
for m,row in rows.items():
 if not row['source']:continue
 if row['private']:
  resolution=dict(path='docs/research/v8-r0-zk-20261009/lean/'+m.replace('.','/')+'.lean',authority='op223 job-owned module source')
 else:
  resolution=mapping.get(m) or d['resolved'].get(row['source_sha256'])
  if not resolution and m.startswith('R1Z.'):
   candidate=('docs/research/100bit-spend-path-20261013/lean/prover-rw-20261023/'+m.split('.')[-1]+'.lean') if m.startswith('R1Z.ProverRwFull') else 'docs/research/v8-r0-zk-20261009/lean/'+m.replace('.','/')+'.lean'
   if Path(candidate).exists() and hashlib.sha256(Path(candidate).read_bytes()).hexdigest()==row['source_sha256']:
    resolution=dict(path=candidate,authority='read-only exact source byte identity to integrated canonical R1Z file; no shared installation')
  if not resolution and m.startswith(('Aeneas.','AeneasMeta.')) or (not resolution and m=='Aeneas'):
   row['external_library']='Aeneas toolchain library, not a repository merge input';continue
 if not resolution:unresolved.append(m);continue
 row['resolution']=resolution;p=resolution['path']
 def at(rev):
  r=subprocess.run(['git','show',rev+':'+p],capture_output=True);return r.stdout if r.returncode==0 else None
 before=at('da6decdc6f');after=at('0c9dc9a4cc')
 row['before_sha256']=hashlib.sha256(before).hexdigest() if before is not None else None
 row['integrated_sha256']=hashlib.sha256(after).hexdigest() if after is not None else None
 row['changed_in_merge']=before!=after
 if before!=after:changed.append(dict(module=m,path=p,before=row['before_sha256'],after=row['integrated_sha256']))
 if row['integrated_sha256']!=row['source_sha256']:dirty.append(m)
report=dict(base='da6decdc6f',integrated='0c9dc9a4cc',roots=['R1Z.PV_Op223_Source.op223_source','R1Z.PV_Op223_V164.refinement'],changed_imported_sources=changed,unresolved_source_authorities=unresolved,source_variant_differences=dirty,modules=rows,shared_source_writes=0)
(E/'lean-import-audit.json').write_text(json.dumps(report,indent=2)+'\n');print(json.dumps({k:v for k,v in report.items() if k!='modules'},indent=2));print('modules',len(rows))
