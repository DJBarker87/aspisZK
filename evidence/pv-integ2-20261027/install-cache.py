from pathlib import Path
import json,subprocess,hashlib,os
D=Path('/home/dombarker/project-offloads/codex-pv-integ2-20261027');J=D.parent/'aspis-joint-20261019';O=D/'objects'
assert not O.exists()
subprocess.run(['cp','-al',str(J/'objects'),str(O)],check=True)
rows=json.loads((D/'cache-inventory.json').read_text());used=[];missing=[]
for r in rows:
 n=r['module'];rel=Path(n.replace('.','/')+'.olean');target=O/rel
 if target.is_file():
  used.append(dict(module=n,source_sha256=r['expected']['sha256'],object=str(target),origin=str(J/'objects'/rel),object_sha256=hashlib.sha256(target.read_bytes()).hexdigest(),source_confirmation='source bytes present and equal' if any(s['sha256']==r['expected']['sha256'] for s in r['available'][0]['sources']) else 'inherited unchanged module; shared source absent; historical receipt retained'))
  continue
 options=r['available']
 if options:
  chosen=next((a for a in options if any(s['sha256']==r['expected']['sha256'] for s in a['sources'])),None)
  assert chosen is not None,(n,'no source-matching private object')
  p=Path(chosen['object']);target.parent.mkdir(parents=True,exist_ok=True)
  for suffix in ['', '.private','.server']:
   src=Path(str(p)+suffix);dst=Path(str(target)+suffix)
   if src.is_file():os.link(src,dst)
  used.append(dict(module=n,source_sha256=r['expected']['sha256'],origin=str(p),object=str(target),object_sha256=chosen['sha256'],source_confirmation='source bytes present and equal'))
 else:missing.append(n)
(D/'cache-reuse.json').write_text(json.dumps(used,indent=2)+'\n')
(D/'missing-objects.json').write_text(json.dumps(missing,indent=2)+'\n')
print('retained',len(used),'missing',len(missing))
