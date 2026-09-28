#!/usr/bin/env python3
"""Reuse R33's source-locked objects; compile only the two new dependencies."""
import argparse,hashlib,json,os,shutil,subprocess
from pathlib import Path
p=argparse.ArgumentParser();p.add_argument('--sources',type=Path,required=True);p.add_argument('--output',type=Path,required=True);p.add_argument('--reuse',type=Path,required=True);a=p.parse_args();assert not a.output.exists();a.output.mkdir()
retained=Path('/home/dombarker/project-offloads/aspis-pool-single-decode-20260825-a3/AspisFormal');workspace=a.output/'workspace';workspace.mkdir()
(workspace/'lakefile.toml').write_text('name = "r34_focused"\nversion = "0.0.0"\n');shutil.copy2(retained/'lean-toolchain',workspace/'lean-toolchain');cache=a.output/'lib';cache.mkdir()
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
old=json.loads((a.reuse/'metadata.json').read_text());records=[]
deps=sorted((retained/'.lake/packages').glob('*/.lake/build/lib/lean'))
env=dict(os.environ,PATH='/home/dombarker/.elan/bin:/usr/bin:/bin',NO_DNA='1',LEAN_PATH=':'.join(map(str,[cache,*deps])))
targets=list(dict.fromkeys([r['target_name']for r in old]+['AspisV8R19/BetaUniformCorrection','AspisV8R19/LowResidualFactor']))
for name in targets:
    src=a.sources/(name+'.lean');obj=cache/(name+'.olean');obj.parent.mkdir(parents=True,exist_ok=True)
    found=next((r for r in old if r['target_name']==name and r['exit']==0 and r['source_sha256']==sha(src)),None)
    if found:
        assert found['toolchain']==(workspace/'lean-toolchain').read_text().strip()
        for f in (a.reuse/'lib'/name).parent.glob(Path(name).name+'.*'):shutil.copy2(f,obj.parent/f.name)
        records.append(found);continue
    cmd=['/home/dombarker/.elan/bin/lake','env','lean','-R',str(a.sources),'-o',str(obj),str(src)]
    log=a.output/(Path(name).name+'.log')
    with log.open('w')as f:r=subprocess.run(['/usr/bin/time','-v',*cmd],cwd=workspace,env=env,stdout=f,stderr=subprocess.STDOUT)
    records.append({'target':str(src),'target_name':name,'source_sha256':sha(src),'command':cmd,'exit':r.returncode,'base_revision':'03549062720acd4fe4ca87f1eac82391e069f2ca','toolchain':(workspace/'lean-toolchain').read_text().strip()})
    (a.output/'metadata.json').write_text(json.dumps(records,indent=2)+'\n');print(log.read_text(),flush=True)
    if r.returncode:raise SystemExit(r.returncode)
