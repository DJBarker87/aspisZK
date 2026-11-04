#!/usr/bin/env python3
import sys,json,hashlib,subprocess,time,shutil
from pathlib import Path
D=Path('/home/dombarker/project-offloads/codex-pv-mf-20261029')
if len(sys.argv)==1:
 with (D/'native03-admission.log').open('a') as f:r=subprocess.run(['python3','/home/dombarker/project-offloads/codex-cx-prover-rw-20261023/src/tools/prover-rw-20261023/native-entropy/reservation.py',str(D/'native03-admission.json')],stdout=f,stderr=subprocess.STDOUT)
 if r.returncode:sys.exit(r.returncode)
 if json.loads((D/'native03-admission.json').read_text()).get('allowed') is not True:sys.exit(78)
 sys.exit(subprocess.run(['systemd-run','--user','--scope','--unit=pv-mf-native03','-q','-p','MemoryHigh=6G','-p','MemoryMax=8G','-p','MemorySwapMax=0','-p','TasksMax=64','python3',str(D/'PV_MF_rehash.py'),'inside']).returncode)
cg=Path('/sys/fs/cgroup'+Path('/proc/self/cgroup').read_text().strip().split('::')[-1]);t=time.monotonic();rows=[]
artifacts=json.loads((D/'artifacts.json').read_text())
(D/'bin').mkdir(exist_ok=True)
old=Path(artifacts[0]['path']); retained=D/'bin/devnet_spend'
if old!=retained:shutil.copy2(old,retained)
artifacts[0]['path']=str(retained)
(D/'artifacts.json').write_text(json.dumps(artifacts,indent=2)+'\n')
features=[]
for p in sorted((D/'target/release/.fingerprint').glob('*/*.json')):
 try:features.append({'path':str(p.relative_to(D/'target')),'record':json.loads(p.read_text())})
 except (ValueError,OSError):pass
if features:(D/'resolved-features.json').write_text(json.dumps(features,indent=2)+'\n')
for r in artifacts:
 p=Path(r['path']);h=hashlib.sha256(p.read_bytes()).hexdigest();rows.append(dict(name=r['name'],path=str(p),sha256=h,bytes=p.stat().st_size,matches=h==r['expected']))
rc=0 if all(r['matches'] for r in rows) else 1
rec=dict(target='V346 fresh four-artifact hash verification',exit=rc,wall_seconds=time.monotonic()-t,source_revision='85addf5a9764aa5e17d28bd6cf96bbda084447c5',print_axioms='N/A native hashes only',peak_cgroup_bytes=(cg/'memory.peak').read_text().strip(),swap_current_bytes=(cg/'memory.swap.current').read_text().strip(),limits={k:(cg/k).read_text().strip() for k in ['memory.high','memory.max','memory.swap.max','pids.max']},artifacts=rows)
(D/'native03-receipt.json').write_text(json.dumps(rec,indent=2)+'\n');print(json.dumps(rec));sys.exit(rc)
