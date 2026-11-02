"""Pin each unique direct/transitive consumer source on every census ref."""
from pathlib import Path
import json,subprocess,hashlib
R=Path(__file__).resolve().parents[2];E=R/'evidence/pv-rdcd7-20261102';x=json.load(open(E/'CONSUMERS-census.json'));variants={}
for row in x['results']:
 if not row['lean_direct_files']:continue
 rev=row['revision'];paths=set(row['lean_direct_files'])
 for mod in row['reverse_import_cone']:paths.add('docs/research/v8-r0-zk-20261009/lean/'+mod.replace('.','/')+'.lean')
 for line in (E/row['grep_file']).read_text().splitlines():paths.add(line[len(rev)+1:].split(':',1)[0])
 for path in sorted(paths):
  q=subprocess.run(['git','show',rev+':'+path],cwd=R,capture_output=True);assert q.returncode==0,(rev,path)
  h=hashlib.sha256(q.stdout).hexdigest();key=path+'@'+h
  if key not in variants:variants[key]=dict(path=path,sha256=h,blob=subprocess.check_output(['git','rev-parse',rev+':'+path],cwd=R,text=True).strip(),occurrences=[])
  variants[key]['occurrences'].append(dict(revision=rev,refs=row['refs']))
(E/'CONSUMER-variants.json').write_text(json.dumps(list(variants.values()),indent=2)+'\n')
print(len(variants),'unique source variants')
for p in sorted({v['path'] for v in variants.values()}):
 n=sum(v['path']==p for v in variants.values())
 if n>1:print(n,p)
