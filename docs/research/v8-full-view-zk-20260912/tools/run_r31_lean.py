#!/usr/bin/env python3
"""Reuse the audited R30 source model object, compile inverse then chord bridge."""
import argparse,hashlib,json,os,shutil,subprocess
from pathlib import Path
p=argparse.ArgumentParser();p.add_argument('--sources',type=Path,required=True);p.add_argument('--output',type=Path,required=True);a=p.parse_args();assert not a.output.exists();a.output.mkdir()
workspace=Path('/home/dombarker/project-offloads/aeneas-patched11-inspect/backends/lean');cache=a.output/'lib';cache.mkdir()
old=Path('/home/dombarker/project-offloads/aspis-r30-lean-20260928-b')
metadata=json.loads((old/'metadata.json').read_text())[0]
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
assert metadata['exit']==0 and metadata['source_sha256']==sha(a.sources/'AspisV8R17/SourceScatter.lean')
assert metadata['toolchain']==(workspace/'lean-toolchain').read_text().strip()
obj=cache/'AspisV8R17/SourceScatter.olean';obj.parent.mkdir();shutil.copy2(old/'lib/AspisV8R17/SourceScatter.olean',obj)
(a.output/'reused-object.json').write_text(json.dumps({'old_receipt':str(old),'source_sha256':metadata['source_sha256'],'object_sha256':sha(obj)},indent=2)+'\n')
env=dict(os.environ,PATH='/home/dombarker/.elan/bin:/usr/bin:/bin',NO_DNA='1',LEAN_PATH=str(cache))
records=[]
for name in ['AspisV8R19/SparseGCoreInverse','AspisV8R19/SparseGChordWitness']:
    src=a.sources/(name+'.lean');obj=cache/(name+'.olean');obj.parent.mkdir(parents=True,exist_ok=True)
    cmd=['/home/dombarker/.elan/bin/lake','env','lean','-R',str(a.sources),'-o',str(obj),str(src)]
    log=a.output/(Path(name).name+'.log')
    with log.open('w')as f:r=subprocess.run(['/usr/bin/time','-v',*cmd],cwd=workspace,env=env,stdout=f,stderr=subprocess.STDOUT)
    rec={'target':str(src),'source_sha256':sha(src),'command':cmd,'exit':r.returncode,'base_revision':'331866cfbe3269add68e9ce7c8e050a5e96fdfaa','toolchain':(workspace/'lean-toolchain').read_text().strip()};records.append(rec)
    (a.output/'metadata.json').write_text(json.dumps(records,indent=2)+'\n');print(log.read_text(),flush=True)
    if r.returncode:raise SystemExit(r.returncode)
