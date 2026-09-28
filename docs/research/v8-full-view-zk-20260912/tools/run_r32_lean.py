#!/usr/bin/env python3
"""Focused polynomial bridge in the existing complete v4.32 cache. No lake build."""
import argparse,hashlib,json,os,shutil,subprocess
from pathlib import Path
p=argparse.ArgumentParser();p.add_argument('--sources',type=Path,required=True);p.add_argument('--output',type=Path,required=True);p.add_argument('--reuse',type=Path);a=p.parse_args();assert not a.output.exists();a.output.mkdir()
retained=Path('/home/dombarker/project-offloads/aspis-pool-single-decode-20260825-a3/AspisFormal')
# Exported caches have no .git directories. Never ask Lake to resolve their
# dependency manifests: it may replace the export on a URL mismatch.
workspace=a.output/'workspace';workspace.mkdir()
(workspace/'lakefile.toml').write_text('name = "r32_focused"\nversion = "0.0.0"\n')
shutil.copy2(retained/'lean-toolchain',workspace/'lean-toolchain')
cache=a.output/'lib';cache.mkdir()
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
targets=['AspisV8R17/SourceScatter','AspisV8R17/IndexSchedule','AspisV8R16/BalancedTransport','AspisV8R17/WeightedScatter','AspisV8R17/ActiveEntry','AspisV8R17/MinorDegree','AspisV8R19/SparseGCoreInverse','AspisV8R19/SparseGChordWitness','AspisV8R19/SparseGPolynomial']
deps=sorted((retained/'.lake/packages').glob('*/.lake/build/lib/lean'))
assert any((d/'Mathlib/LinearAlgebra/Matrix/NonsingularInverse.olean').is_file()for d in deps)
env=dict(os.environ,PATH='/home/dombarker/.elan/bin:/usr/bin:/bin',NO_DNA='1',LEAN_PATH=':'.join(map(str,[cache,*deps])))
reused=[];records=[];old=[] if not a.reuse else json.loads((a.reuse/'metadata.json').read_text())
for name in targets:
    src=a.sources/(name+'.lean');obj=cache/(name+'.olean');obj.parent.mkdir(parents=True,exist_ok=True)
    found=next((r for r in old if r['target_name']==name and r['exit']==0 and r['source_sha256']==sha(src)),None)
    if found:
        assert found['toolchain']==(workspace/'lean-toolchain').read_text().strip()
        for f in (a.reuse/'lib'/name).parent.glob(Path(name).name+'.*'):shutil.copy2(f,obj.parent/f.name)
        reused.append(found);continue
    cmd=['/home/dombarker/.elan/bin/lake','env','lean','-R',str(a.sources),'-o',str(obj),str(src)]
    log=a.output/(Path(name).name+'.log')
    with log.open('w')as f:r=subprocess.run(['/usr/bin/time','-v',*cmd],cwd=workspace,env=env,stdout=f,stderr=subprocess.STDOUT)
    rec={'target':str(src),'target_name':name,'source_sha256':sha(src),'command':cmd,'exit':r.returncode,'base_revision':'66727edcc16549a5dd251dc1eca3d2d2e2c57ad5','toolchain':(workspace/'lean-toolchain').read_text().strip()};records.append(rec)
    (a.output/'metadata.json').write_text(json.dumps(reused+records,indent=2)+'\n')
    (a.output/'reused.json').write_text(json.dumps({'from':str(a.reuse),'records':reused},indent=2)+'\n')
    print(log.read_text(),flush=True)
    if r.returncode:raise SystemExit(r.returncode)
