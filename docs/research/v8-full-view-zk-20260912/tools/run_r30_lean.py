#!/usr/bin/env python3
"""Compile the reused small source model once, then its new support theorem."""
import argparse,hashlib,json,os,shutil,subprocess
from pathlib import Path
p=argparse.ArgumentParser();p.add_argument('--sources',type=Path,required=True);p.add_argument('--output',type=Path,required=True);a=p.parse_args();assert not a.output.exists();a.output.mkdir()
workspace=Path('/home/dombarker/project-offloads/aeneas-patched11-inspect/backends/lean');cache=a.output/'lib';cache.mkdir()
env=dict(os.environ,PATH='/home/dombarker/.elan/bin:/usr/bin:/bin',NO_DNA='1',LEAN_PATH=str(cache))
records=[]
for name in ['AspisV8R17/SourceScatter','AspisV8R19/LowKernelSeparation']:
    src=a.sources/(name+'.lean');obj=cache/(name+'.olean');obj.parent.mkdir(parents=True,exist_ok=True)
    cmd=['/home/dombarker/.elan/bin/lake','env','lean','-R',str(a.sources),'-o',str(obj),str(src)]
    log=a.output/(Path(name).name+'.log')
    with log.open('w')as f:r=subprocess.run(['/usr/bin/time','-v',*cmd],cwd=workspace,env=env,stdout=f,stderr=subprocess.STDOUT)
    rec={'target':str(src),'source_sha256':hashlib.sha256(src.read_bytes()).hexdigest(),'command':cmd,'exit':r.returncode,'base_revision':'5cf16f1796e14d8d05aa485b0a7d6ca86f5b27df','toolchain':(workspace/'lean-toolchain').read_text().strip()};records.append(rec)
    (a.output/'metadata.json').write_text(json.dumps(records,indent=2)+'\n');print(log.read_text(),flush=True)
    if r.returncode:raise SystemExit(r.returncode)
