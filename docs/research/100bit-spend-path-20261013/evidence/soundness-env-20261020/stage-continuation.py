"""Host-only staging of explicitly selected sources; snapshots any replacement."""
import json,hashlib,shutil
from pathlib import Path
J=Path('/home/dombarker/project-offloads/aspis-joint-20261019'); D=J/'evidence-S'; S=J/'sources-S'; incoming=D/'incoming-env2'; snap=J/'snapshots/codex-cx-soundness-env2-20261020'; snap.mkdir(parents=True,exist_ok=True)
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
man=json.loads((D/'manifest-S.json').read_text()); changes=[]
for e in man['order']:
 rel=e['module'].replace('.','/')+'.lean'; src=incoming/rel; dst=S/rel
 assert sha(src)==e['sha256']
 if dst.exists() and sha(dst)==sha(src):continue
 if dst.exists():
  q=snap/'sources-S'/rel;q.parent.mkdir(parents=True,exist_ok=True);shutil.copy2(dst,q)
 changes.append({'module':e['module'],'old_sha256':sha(dst) if dst.exists() else None,'new_sha256':sha(src),'source':e['source']})
 dst.parent.mkdir(parents=True,exist_ok=True);shutil.copy2(src,dst)
# External CompPoly cache is the pinned one used by the accepted extractor packets.
p=Path('/home/dombarker/project-offloads/r1-privacy-build-integration-20261019/env/S.json');env=json.loads(p.read_text());shutil.copy2(p,snap/'env-S.json')
cache='/home/dombarker/project-offloads/root-comppoly432-retained-cache-20261019'
if cache not in env['LEAN_PATH'].split(':'):env['LEAN_PATH']=cache+':'+env['LEAN_PATH']
p.write_text(json.dumps(env,indent=1)+'\n')
lib={}
for m in man['libraries']:
 hit=next((Path(d)/(m.replace('.','/')+'.olean') for d in env['LEAN_PATH'].split(':') if (Path(d)/(m.replace('.','/')+'.olean')).exists()),None)
 assert hit,m
 lib[m]={'path':str(hit),'sha256':sha(hit),'size':hit.stat().st_size}
(D/'continuation-libraries.json').write_text(json.dumps(lib,indent=2)+'\n')
(D/'continuation-staging.json').write_text(json.dumps(changes,indent=2)+'\n')
# Preserve launcher and install a new inode; no running shell reads a changed script.
p=D/'run-S.sh';s=p.read_text();shutil.copy2(p,snap/'run-S.sh')
s=s.replace('[ "$A" -ge 6450 ] && [ "$A" -le 6999 ]','[ "$A" -ge 7000 ] && [ "$A" -le 7999 ]')
start=s.index('# Preserve enough assigned attempts');end=s.index('[ -e "$T/evidence/out-$A.log"',start)
s=s[:start]+s[end:]
q=D/'run-S-env2.sh';q.write_text(s);q.replace(p)
(D/'run-S-env2.sh').write_text(s)
print('staged',len(changes),'libraries',len(lib))
