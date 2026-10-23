from pathlib import Path
import os,sys,json,hashlib,subprocess,re
H=Path('/home/dombarker/project-offloads/codex-cx-real-r3-20261023'); E=H/'evidence';J=Path('/home/dombarker/project-offloads/aspis-joint-20261019');T=Path('/home/dombarker/project-offloads/aspis-fs-generic-20261006/evidence')
a=int(sys.argv[1]);m=sys.argv[2];assert 11100<=a<=11199 and 'RealR3_' in m
src=J/'sources'/(m+'.lean');s=src.read_text(); deps=[]
for line in s.splitlines():
 if line.startswith('import '):
  for mod in line[7:].split():
   obj=J/'objects'/(mod.replace('.','/')+'.olean');p=J/'sources'/(mod.replace('.','/')+'.lean')
   assert obj.exists(),obj
   deps.append({'module':mod,'object_sha256':hashlib.sha256(obj.read_bytes()).hexdigest(),'source_sha256':hashlib.sha256(p.read_bytes()).hexdigest()})
fp=hashlib.sha256(json.dumps(deps,sort_keys=True).encode()).hexdigest()[:16]
(E/(str(a)+'-input.json')).write_text(json.dumps({'source_revision':(H/'revision.txt').read_text().strip(),'source_sha256':hashlib.sha256(src.read_bytes()).hexdigest(),'dependencies':deps,'deps_fingerprint':fp},indent=2)+'\n')
(E/'lean-snapshots').mkdir(exist_ok=True);(E/'lean-snapshots'/f'{a}.lean.txt').write_text(s)
cmd=['sh',str(E/'RealR3_run-joint.sh'),str(a),m,'J','7000','8',fp]
p=subprocess.run(cmd,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
(E/(str(a)+'-launcher.log')).write_text(p.stdout);print(p.stdout)
for kind in ['out','time','sha']:
 pth=T/(f'{kind}-{a}.'+('txt' if kind=='sha' else 'log'))
 if pth.exists():(E/pth.name).write_bytes(pth.read_bytes())
