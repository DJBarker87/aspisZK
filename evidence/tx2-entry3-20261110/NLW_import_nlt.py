from NLW_transport import *
import hashlib,lzma,base64
rev='b2cc16dbe3f6352954d85a7e9a47088ff193401b'
paths=subprocess.check_output(['git','ls-tree','-r','--name-only',rev,'evidence/tx2-common2-20261110'],text=True).splitlines()
source={}
for n in paths:
 if '/sources/' not in n and n.endswith('.lean'):
  raw=subprocess.check_output(['git','show',rev+':'+n]);h=hashlib.sha256(raw).hexdigest();p=E/'NLW_INPUTS'/(h+'.xz')
  if not p.exists():p.write_bytes(lzma.compress(raw))
  source[Path(n).stem]=dict(path=n,sha256=h,bytes=len(raw),archive=str(p.relative_to(E)))
pathraw=subprocess.check_output(['git','show',rev+':evidence/tx2-common2-20261110/NLT_PATHS.json'],text=True)
foreign=json.loads(pathraw)
allsource=source;needed=set();todo=['NLT_Root']
while todo:
 n=todo.pop()
 if n in needed:continue
 needed.add(n);raw=lzma.decompress((E/allsource[n]['archive']).read_bytes()).decode()
 import re
 todo += [d for d in re.findall(r'^import (NLT_\w+)',raw,re.M) if d not in needed]
source={n:allsource[n] for n in sorted(needed)}
admission('NLW_S005')
r=ssh('python3',f'''from pathlib import Path
import json,hashlib,shutil
b=Path({B!r});src=Path({foreign[0]!r});dst=b/'NLW_seed'/'NLT';rows=[]
mods=json.loads({json.dumps(list(source))!r})
for name in mods:
 p=src/(name+'.olean');assert p.is_file(),p
 for z in [p,Path(str(p)+'.private'),Path(str(p)+'.server'),p.with_suffix('.ir')]:
  if not z.is_file():continue
  q=dst/z.name;q.parent.mkdir(parents=True,exist_ok=True);shutil.copy2(z,q)
  rows.append(dict(source=str(z),destination=str(q),bytes=q.stat().st_size,sha256=hashlib.sha256(q.read_bytes()).hexdigest()))
print(json.dumps(rows))
''')
assert r.returncode==0,r.stderr
rows=json.loads(r.stdout);(E/'NLW_NLT_IMPORT.json').write_text(json.dumps(dict(revision=rev,source=source,objects=rows,bytes=sum(x['bytes'] for x in rows),status='DEFINITION_REUSE_ONLY_UNGATED_ROOT_NOT_CREDITED'),indent=1))
x=json.loads((E/'NLW_ENV.json').read_text());old=x['LEAN_PATH'].split(':');x['LEAN_PATH']=':'.join(dict.fromkeys(old[:4]+[B+'/NLW_seed/NLT']+foreign[1:]+old[4:]));(E/'NLW_ENV.json').write_text(json.dumps(x,indent=1))
print(json.dumps(dict(modules=len(source),objects=len(rows),bytes=sum(x['bytes'] for x in rows))))
