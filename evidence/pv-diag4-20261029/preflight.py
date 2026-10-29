from pathlib import Path
import json,hashlib,os,re
D=Path('/home/dombarker/project-offloads/codex-pv-diag4-20261029');B=D.parent
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
rows=json.loads((D/'external-authority.json').read_text());out=[];bad=[]
for r in ([] if '--ids-only' in __import__('sys').argv else rows):
 p=Path(r['path']);actual=sha(p) if p.exists() else None
 if actual!=r['object_sha256']:bad.append(dict(**r,actual=actual))
 out.append(dict(module=r['module'],path=str(p),sha256=actual))
(D/('external-preflight-ids-only.json' if '--ids-only' in __import__('sys').argv else 'external-preflight.json')).write_text(json.dumps(dict(checked=len(out),mismatches=bad,manifest_sha256=sha(D/'external-authority.json')),indent=2)+'\n')
# Check the entire assigned block against other job receipts/sent ledgers.
hits=[]
for root,dirs,files in os.walk(B):
 p=Path(root)
 if p==D:dirs[:]=[];continue
 if len(p.relative_to(B).parts)>=5:dirs[:]=[]
 dirs[:]=[d for d in dirs if d not in {'target','client-target','objects','lean-objects','actual-objects','sources','actual-sources','source','src','node_modules','.git','.lake','native-source','repo','frozen'}]
 for name in dirs+files:
  if re.search(r'(?<![A-Za-z0-9])645\d\d(?![A-Za-z0-9])',name):hits.append(str(p/name))
 for name in files:
  if name=='sent.txt':
   for line in (p/name).read_text().splitlines():
    fields=line.split()
    if len(fields)>2 and fields[2].isdigit() and 64500<=int(fields[2])<=64599:hits.append(str(p/name)+':'+line)
(D/'id-preflight.json').write_text(json.dumps(dict(range=[64500,64599],collisions=hits),indent=2)+'\n')
print('external objects',len(out),'mismatches',len(bad),'ID collisions',len(hits))
assert not bad and not hits
