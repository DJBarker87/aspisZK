from pathlib import Path
import subprocess,json,hashlib,re,shlex
here=Path(__file__).resolve().parent
root=here.parents[1]
modules=['R1Z/PrivacyR1AcctBasis','R1Z/PrivacyR1AcctModel','R1Z/PrivacyR1HeadlineAcct']
code='''import pathlib,hashlib,json,re
j=pathlib.Path('/home/dombarker/project-offloads/aspis-joint-20261019')
mods=MODS
rows=[]
for m in mods:
 s=j/'sources'/(m+'.lean'); o=j/'objects'/(m+'.olean')
 im=sorted(re.findall(r'^import (\\S+)',s.read_text(),re.M))
 deps=[]
 for d in im:
  ds=j/'sources'/(d.replace('.','/')+'.lean'); do=j/'objects'/(d.replace('.','/')+'.olean')
  deps.append(dict(module=d,source_sha256=hashlib.sha256(ds.read_bytes()).hexdigest() if ds.exists() else None,object_sha256=hashlib.sha256(do.read_bytes()).hexdigest(),object_bytes=do.stat().st_size))
 fp=hashlib.sha256(';'.join(d['module']+'='+d['object_sha256'] for d in deps).encode()).hexdigest()[:16]
 rows.append(dict(module=m,source_sha256=hashlib.sha256(s.read_bytes()).hexdigest(),object_sha256=hashlib.sha256(o.read_bytes()).hexdigest(),object_bytes=o.stat().st_size,deps_fingerprint=fp,imports=deps))
print(json.dumps(rows,indent=2))
'''.replace('MODS',repr(modules))
rows=json.loads(subprocess.check_output(['ssh','dombarker@100.108.41.90','python3 -c '+shlex.quote(code)],text=True))
receipts=[json.loads(l) for l in (here/'attempts.jsonl').read_text().splitlines()]
for r in rows:
 local=root/'lean'/(r['module']+'.lean')
 assert hashlib.sha256(local.read_bytes()).hexdigest()==r['source_sha256']
 receipt=next(x for x in reversed(receipts) if x['module']==r['module'] and x['exit']=='0')
 assert receipt['source_sha256']==r['source_sha256']
 assert receipt['deps_fingerprint']==r['deps_fingerprint']
 r['successful_attempt']=receipt['attempt']
 r['source_commit']=subprocess.check_output(['git','log','-1','--format=%H','--',str(local)],text=True).strip()
 for d in r['imports']:
  p=root/'lean'/(d['module'].replace('.','/')+'.lean')
  if p.exists(): assert hashlib.sha256(p.read_bytes()).hexdigest()==d['source_sha256']
(here/'frozen-objects.json').write_text(json.dumps(rows,indent=2)+'\n')
print('Source and direct-import fingerprints match all three successful receipts.')
