#!/usr/bin/env python3
"""One focused release replay, using the R62 cache and full Aeneas runtime.
Run under MemoryHigh=5G, MemoryMax=7G, MemorySwapMax=0, TasksMax=128.
No lake build or dependency compilation occurs.
"""
import argparse, hashlib, json, os, re, shutil, subprocess
from pathlib import Path
from audit_r63_source import check

p=argparse.ArgumentParser();p.add_argument('--output',type=Path,required=True);a=p.parse_args()
root=Path('/home/dombarker/project-offloads')
sources=root/'aspis-r57-lean-src-20260929-a'
reuse=root/'aspis-r62-lean-20260929-a'
runtime=root/'v7-tag73-challenge-qm31-source-20260825-work/toolchain/aeneas-full/backends/lean'
retained=root/'aspis-pool-single-decode-20260825-a3/AspisFormal'
stage=root/'aspis-v7-aeneas-source-unblock-20260830/staged-current-normalized-statement-owned-twohelpers-r19/V7Tag73CurrentHelpersOpaque'
selected=root/'aspis-r20-r62-gather-20260929-b'
base='491ccd3d42e2e07ff2c04cb6dd17c7ea20269ed0'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
assert not a.output.exists();a.output.mkdir()
manifest=json.loads((selected/'r18-stage.json').read_text())
for n,h in manifest['files'].items():assert sha(selected/n)==h,n
audit=check(stage,sources/'AspisV8R19/InverseFieldSlice.lean',selected/'crates/aspis-core/src/field.rs',sources/'AspisV8R19/InverseChain.lean')
(a.output/'source-audit.json').write_text(json.dumps(audit,indent=2)+'\n')
cache=a.output/'lib';cache.mkdir();records=json.loads((reuse/'metadata.json').read_text())
for r in records:
    assert r['exit']==0 and r['toolchain']=='leanprover/lean4:v4.32.0'
    assert sha(sources/(r['target_name']+'.lean'))==r['source_sha256']
shutil.copytree(reuse/'lib',cache,dirs_exist_ok=True)
workspace=a.output/'workspace';workspace.mkdir()
(workspace/'lakefile.toml').write_text('name = "r63_focused"\nversion = "0.0.0"\n')
shutil.copy2(retained/'lean-toolchain',workspace/'lean-toolchain')
deps=sorted((retained/'.lake/packages').glob('*/.lake/build/lib/lean'))
env=dict(os.environ,PATH='/home/dombarker/.elan/bin:/usr/bin:/bin',NO_DNA='1',
    LEAN_PATH=':'.join(map(str,[cache,*deps,runtime/'.lake/build/lib/lean'])))
targets=['AspisV8R19/'+n for n in ['InverseFieldSlice','InverseRuntimeMul','GeneratedInverseLoop']]
# Pin every transitively imported local/runtime source and each used runtime object.
pins={};seen=set()
def visit(module):
    if module in seen:return
    seen.add(module);rel=module.replace('.','/')+'.lean'
    owner=next((d for d in [sources,runtime] if (d/rel).is_file()),None)
    if owner is None:return
    src=owner/rel;pins[str(src)]=sha(src)
    if owner==runtime:
        obj=runtime/'.lake/build/lib/lean'/rel.replace('.lean','.olean')
        assert obj.is_file(),obj;pins[str(obj)]=sha(obj)
    for line in src.read_text().splitlines():
        if re.match(r'^(public )?import ',line):
            for name in line.split('import ',1)[1].split(): visit(name)
for n in targets:visit(n.replace('/','.'))
(a.output/'dependency-pins.json').write_text(json.dumps(pins,indent=2)+'\n')
for name in targets:
    src=sources/(name+'.lean');obj=cache/(name+'.olean');obj.parent.mkdir(parents=True,exist_ok=True)
    cmd=['/home/dombarker/.elan/bin/lake','env','lean','-j1','-M4500','-R',str(sources),'-o',str(obj),str(src)]
    logpath=a.output/(Path(name).name+'.log')
    with logpath.open('w') as f:r=subprocess.run(['/usr/bin/time','-v',*cmd],cwd=workspace,env=env,stdout=f,stderr=subprocess.STDOUT)
    records.append({'target_name':name,'source_sha256':sha(src),'exit':r.returncode,'command':cmd,
        'base_revision':base,'toolchain':(workspace/'lean-toolchain').read_text().strip()})
    (a.output/'metadata.json').write_text(json.dumps(records,indent=2)+'\n')
    print(logpath.read_text(),flush=True)
    if r.returncode:raise SystemExit(r.returncode)
    assert 'sorryAx' not in logpath.read_text()
for name,h in pins.items():assert sha(Path(name))==h,name
print(json.dumps({'status':'PASS','cached':len(records)-3,'compiled':3,'dependency_pins':len(pins)}))
