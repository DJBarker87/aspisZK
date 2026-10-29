from pathlib import Path
import json,hashlib,re,os
D=Path('/home/dombarker/project-offloads/codex-pv-diag10-20261029');P=D.parent/'codex-pv-diag5-20261029'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
assert not (D/'objects').exists()
(D/'sources').mkdir(exist_ok=True);(D/'objects').mkdir()
env=json.loads((P/'env-J.json').read_text());env['LEAN_PATH']=str(D/'objects')+':'+str(D.parent/'codex-pv-runjoin-20261026/runjoin32-lean/external');(D/'env-J.json').write_text(json.dumps(env,indent=2)+'\n')
ext=json.loads((P/'external-authority.json').read_text());bad=[]
for r in ext:
 if sha(Path(r['path']))!=r['object_sha256']:bad.append(r['module'])
(D/'external-preflight.json').write_text(json.dumps(dict(checked=len(ext),manifest_sha256=sha(P/'external-authority.json'),mismatches=bad),indent=2)+'\n');assert not bad
hits=[]
for root,dirs,files in os.walk(D.parent):
 p=Path(root)
 if p==D:dirs[:]=[];continue
 if len(p.relative_to(D.parent).parts)>=5:dirs[:]=[]
 dirs[:]=[d for d in dirs if d not in {'target','client-target','objects','lean-objects','actual-objects','sources','actual-sources','source','src','node_modules','.git','.lake','native-source','repo','frozen'}]
 for name in dirs+files:
  if re.search(r'(?<![A-Za-z0-9])667\d\d(?![A-Za-z0-9])',name):hits.append(str(p/name))
 for name in files:
  if name=='sent.txt':
   for line in (p/name).read_text().splitlines():
    fields=line.split()
    if len(fields)>2 and fields[2].isdigit() and 66700<=int(fields[2])<=66799:hits.append(str(p/name)+':'+line)
(D/'id-preflight.json').write_text(json.dumps(dict(range=[66700,66799],collisions=hits),indent=2)+'\n');assert not hits
print('external checked',len(ext),'ID collisions',len(hits))
