#!/usr/bin/env python3
"""Bounded-scope host compile and focused source fixture execution.

No whole privacy gate is implied by honest proof construction. The channel
profile's affine audit must bind its additional p0/p2 observations; the R19
stager installs those rows and independent source rechecks explicitly.
"""
import argparse,hashlib,json,os,shutil,subprocess
from pathlib import Path
p=argparse.ArgumentParser(description=__doc__)
p.add_argument('--stage',type=Path,required=True);p.add_argument('--output',type=Path,required=True)
p.add_argument('--generate',action='store_true');p.add_argument('--audit',type=Path,action='append',default=[])
p.add_argument('--world',type=int,choices=[0,1],action='append');p.add_argument('--affine',action='store_true')
a=p.parse_args();root=a.stage.resolve();assert not a.output.exists();a.output.mkdir()
m=json.loads((root/'r18-stage.json').read_text());h=json.loads((root/'r17-stage.json').read_text())
for n,d in m['files'].items():assert hashlib.sha256((root/n).read_bytes()).hexdigest()==d,n
target=Path('/home/dombarker/project-offloads/aspis-v8-performance-20260908.scS2Jz/docs/research/v8-no-work-100-20260907/experiments/performance-host/target')
env=dict(os.environ,PATH='/home/dombarker/.cargo/bin:/usr/bin:/bin',NO_DNA='1',RUSTFLAGS=h['rustflags'],CARGO_TARGET_DIR=str(target))
for n in ['ASPIS_R17_C1_WITNESS_AUDIT','ASPIS_R17_COUPLED_AUDIT','ASPIS_R17_H1_SEMANTIC_AUDIT','ASPIS_V8_MAX_FRONTIER_SCAN','ASPIS_R15_SELECTED_SECOND']:env.pop(n,None)
env['ASPIS_V8_POSITIVE_CASE']='honest'
cmd=['/home/dombarker/.cargo/bin/cargo','build','--offline','--locked','--release','--jobs','2','--features',h['features'],
 '--manifest-path',str(root/'docs/research/v8-no-work-100-20260907/experiments/performance-host/Cargo.toml'),'--bin','aspis-v8-performance-host']
def run(cmd,name):
    print(json.dumps({'phase':name,'command':cmd,'profile':m['profile']}),flush=True)
    with (a.output/(name+'.log')).open('w') as f:subprocess.run(['/usr/bin/time','-v']+cmd,cwd=root,env=env,stdout=f,stderr=subprocess.STDOUT,check=True)
run(cmd,'compile');binary=(a.output/'r19-host').resolve();shutil.copy2(target/'release/aspis-v8-performance-host',binary)
if a.generate:
    for world in a.world or [0,1]:
        env['ASPIS_R16_SELECTED_SECOND']=str(world)
        if a.affine:env['ASPIS_R17_C1_WITNESS_AUDIT']='1'
        fixture=(a.output/f'fixture-world{world}').resolve();run([str(binary),str(fixture)],f'world{world}')
        env.pop('ASPIS_R17_C1_WITNESS_AUDIT',None)
        run([str(binary),'--audit-existing',str(fixture)],f'audit-world{world}')
for i,fixture in enumerate(a.audit):run([str(binary),'--audit-existing',str(fixture)],f'audit-existing-{i}')
(a.output/'host-metadata.json').write_text(json.dumps({'profile':m['profile'],'flags':h['rustflags'],'features':h['features'],
 'binary_sha256':hashlib.sha256(binary.read_bytes()).hexdigest(),'source_manifest_sha256':hashlib.sha256((root/'r18-stage.json').read_bytes()).hexdigest(),
 'full_privacy_proved':False,'full_soundness_proved':False},indent=2)+'\n')
