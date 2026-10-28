from pathlib import Path
import subprocess,json,shlex
E=Path('evidence/pv-batch2-20261027/batch2e');C=E.parent/'batch2c'
code='''import sys,json,hashlib,time
from pathlib import Path
rows=json.load(sys.stdin);D=Path('/home/dombarker/project-offloads/codex-pv-batch2-20261027')
e=json.loads((D/'env-J.json').read_text());roots=[str(D/'lean-objects')]+e['LEAN_PATH'].split(':');bad=[];checked=0;aliases=[]
for a in rows:
 for root in roots:
  p=Path(root)/(a['module']+'.olean')
  if p.exists():break
 else:bad.append(dict(module=a['module'],reason='missing'));continue
 sha=hashlib.sha256(p.read_bytes()).hexdigest();checked+=1
 if sha!=a['object_sha256']:bad.append(dict(module=a['module'],path=str(p),expected=a['object_sha256'],actual=sha))
 elif str(p)!=a['path']:aliases.append(dict(module=a['module'],loaded=str(p),manifest_path=a['path'],sha256=sha,same_inode=p.samefile(a['path'])))
print(json.dumps(dict(epoch=time.time(),checked=checked,mismatches=bad,identical_aliases=aliases,lean_path_prefix=roots)))
'''
r=subprocess.run(['ssh','dombarker@100.108.41.90','python3 -c '+shlex.quote(code)],input=(C/'external-object-manifest.json').read_bytes(),capture_output=True,check=True)
j=json.loads(r.stdout);(E/'H4-ACTUAL-LIBRARY-PATHS.json').write_text(json.dumps(j,indent=2)+'\n');assert not j['mismatches'],j['mismatches'];print('actual external resolutions',j['checked'],'all match')
