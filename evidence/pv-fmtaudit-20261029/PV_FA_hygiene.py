from pathlib import Path
import json,subprocess,re,hashlib,collections
P=Path(__file__).parent;rows=json.loads((P/'closing-source-index.json').read_text());ejr=json.loads((P/'input-EJR_final-inventory.json').read_text());authority={x['module'].replace('/','.'):x['resolution']['path']for x in ejr['selected']if x.get('resolution')}
cache={};trees={};log={}
def read(ref,path):
 key=(ref,path)
 if key not in cache:
  p=subprocess.run(['git','show',ref+':'+path],capture_output=True);cache[key]=p.stdout.decode()if p.returncode==0 else None
 return cache[key]
def resolve(ref,mod):
 if ref not in trees:
  fs=subprocess.check_output(['git','ls-tree','-r','--name-only',ref],text=True).splitlines();trees[ref]=[p for p in fs if p.endswith('.lean')]
 fs=trees[ref];exact=[p for p in fs if p.endswith('/'+mod.replace('.','/')+'.lean')];p=authority.get(mod)
 if p in fs:return p,'EJR-selected path in snapshot'
 if len(exact)==1:return exact[0],'unique module suffix in snapshot (audit traversal only)'
 stem=mod.split('.')[-1]+'.lean';c=[p for p in fs if Path(p).name==stem]
 if len(c)==1:return c[0],'unique filename in snapshot (audit traversal only)'
 return None,dict(candidates=c)
for row in rows:
 if not row['sources']:row['hygiene']='inventory audit row';continue
 src=row['sources'][0];ref=src['ref'];queue=[(m,[row['theorem'].rsplit('.',1)[0],m])for m in src['imports']];seen=set();entry=[];gaps=[]
 while queue:
  m,chain=queue.pop(0)
  if m in seen:continue
  seen.add(m)
  if m.startswith(('Aeneas.','AeneasMeta.'))or m in ['Aeneas','AeneasMeta']:
   entry.append(dict(module=m,chain=chain));continue
  if m.startswith(('Mathlib','Lean','Init','Std','Batteries')):continue
  path,method=resolve(ref,m)
  if path is None:gaps.append(dict(module=m,chain=chain,resolution=method));continue
  s=read(ref,path)
  if s is None:gaps.append(dict(module=m,path=path));continue
  log[ref+':'+path]=dict(sha256=hashlib.sha256(s.encode()).hexdigest(),method=method)
  for imp in re.findall(r'^\s*(?:public )?import (\S+)',s,re.M):queue.append((imp,chain+[imp]))
 row['library_import_entries']=entry;row['import_gaps']=gaps;row['source_modules_visited']=len(seen)
(P/'hygiene-import-paths.json').write_text(json.dumps(rows,indent=1));(P/'hygiene-source-pins.json').write_text(json.dumps(log,indent=1));print('reached Aeneas',sum(bool(x.get('library_import_entries'))for x in rows));print('gaps',[(x['id'],len(x.get('import_gaps',[])))for x in rows if x.get('import_gaps')])
