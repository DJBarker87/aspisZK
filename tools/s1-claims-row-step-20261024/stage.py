#!/usr/bin/env python3
from pathlib import Path
import hashlib,json,subprocess
R=Path(__file__).resolve().parents[2];D=R/'tools/s1-claims-row-step-20261024';P=Path('/tmp/s126-claims-row-payload-20261024');P.mkdir(exist_ok=False)
rev='25866ec331cc7ce27dd9956609c11d32fa8fa58a';files={}
for n in ['r1_semantic.rs','r1_wire.rs']:
 path='crates/aspis-r1-cost-probe/src/'+n;b=subprocess.check_output(['git','-C',str(R),'show',rev+':'+path]);(P/n).write_bytes(b);files[n]=dict(path=path,sha256=hashlib.sha256(b).hexdigest())
(P/'source-pins.json').write_text(json.dumps(dict(revision=rev,frozen_files=files),indent=2)+'\n')
host='dombarker@100.108.41.90';W='/home/dombarker/project-offloads/s126-real-sdk-20261021/s1-claims-row-step-v1-20261024'
subprocess.run(['ssh',host,'mkdir -p '+W],check=True)
subprocess.run(['scp','-q','-r',str(P),host+':'+W+'/payload'],check=True)
for f in ['proofs.rs','run-host.py','admit-host.py','prepare-host.py']:
 subprocess.run(['scp','-q',str(D/f),host+':'+W+'/'+f],check=True)
subprocess.run(['scp','-q',str(R/'tools/s126-host-admission-20261024/HostAdmission.py'),host+':'+W+'/HostAdmission.py'],check=True)
subprocess.run(['ssh',host,'python3 '+W+'/prepare-host.py'],check=True)
