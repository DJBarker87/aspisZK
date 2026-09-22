#!/usr/bin/env python3
"""Bounded NUC scope: compile release, then source comparison/proof/tamper gates."""
import argparse,hashlib,json,os,shutil,subprocess
from pathlib import Path
p=argparse.ArgumentParser();p.add_argument('--stage',type=Path,required=True);p.add_argument('--inputs',type=Path,required=True);p.add_argument('--fixture',type=Path,required=True);p.add_argument('--output',type=Path,required=True);a=p.parse_args()
assert not a.output.exists();a.output.mkdir()
m=json.loads((a.stage/'r18-stage.json').read_text());h=json.loads((a.stage/'r17-stage.json').read_text())
for n,v in m['files'].items():assert hashlib.sha256((a.stage/n).read_bytes()).hexdigest()==v,n
target=Path('/home/dombarker/project-offloads/aspis-v8-performance-20260908.scS2Jz/docs/research/v8-no-work-100-20260907/experiments/performance-host/target')
env=dict(os.environ,NO_DNA='1',PATH='/home/dombarker/.cargo/bin:/usr/bin:/bin',CARGO_TARGET_DIR=str(target),RUSTFLAGS=h['rustflags'])
env.pop('ASPIS_R21_CAPTURE_PUBLIC',None)
cmd=['/home/dombarker/.cargo/bin/cargo','build','--release','--offline','--locked','--jobs','2','--manifest-path',str(a.stage/'docs/research/v8-no-work-100-20260907/experiments/performance-host/Cargo.toml'),'--features',h['features'],'--bin','r21-pilot']
print(json.dumps({'phase':'compile then named public proof/tamper gate','command':cmd,'flags':h['rustflags']}),flush=True)
with (a.output/'compile.log').open('w')as f:subprocess.run(['/usr/bin/time','-v']+cmd,env=env,cwd=a.stage,stdout=f,stderr=subprocess.STDOUT,check=True)
binary=a.output/'r21-pilot';shutil.copy2(target/'release/r21-pilot',binary)
digest=hashlib.sha256(b'Aspis/R21/original-public-instance/v1')
fixtures={}
for n in ['proof-1.bin','public.bin','transition.bin','binding.bin']:
    data=(a.fixture/n).read_bytes();digest.update(len(data).to_bytes(8,'little'));digest.update(data);fixtures[n]=hashlib.sha256(data).hexdigest()
context=a.output/'context.bin';context.write_bytes(digest.digest())
with (a.output/'pilot.log').open('w')as f:subprocess.run(['/usr/bin/time','-v',str(binary),str(a.output/'generated'),str(a.inputs),str(context)],env=env,cwd=a.stage,stdout=f,stderr=subprocess.STDOUT,check=True)
(a.output/'metadata.json').write_text(json.dumps({'binary_sha256':hashlib.sha256(binary.read_bytes()).hexdigest(),'public_inputs_sha256':hashlib.sha256(a.inputs.read_bytes()).hexdigest(),'context_sha256':hashlib.sha256(context.read_bytes()).hexdigest(),'fixtures':fixtures,'source_manifest_sha256':hashlib.sha256((a.stage/'r18-stage.json').read_bytes()).hexdigest(),'scope':'ordinary+image helper only','security_theorem':False},indent=2)+'\n')
