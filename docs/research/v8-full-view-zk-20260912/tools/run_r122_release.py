#!/usr/bin/env python3
"""Compile the two R122 leaves against the frozen R121 cache."""
import argparse, hashlib, json, os, re, shutil, subprocess
from pathlib import Path

p=argparse.ArgumentParser();p.add_argument('--output',type=Path,required=True);a=p.parse_args()
root=Path('/home/dombarker/project-offloads')
sources=root/'aspis-r57-lean-src-20260929-a'
parent=root/'aspis-r121-release-20260930-a'
runtime=root/'v7-tag73-challenge-qm31-source-20260825-work/toolchain/aeneas-full/backends/lean'
retained=root/'aspis-pool-single-decode-20260825-a3/AspisFormal'
manifest=json.loads((Path(__file__).with_name('r122-release-manifest.json')).read_text())
def sha(path):return hashlib.sha256(path.read_bytes()).hexdigest()
assert not a.output.exists();a.output.mkdir(parents=True)
cache=a.output/'lib';shutil.copytree(parent/'lib',cache)
workspace=a.output/'workspace';workspace.mkdir()
(workspace/'lakefile.toml').write_text('name = "r122_release"\nversion = "0.0.0"\n')
shutil.copy2(retained/'lean-toolchain',workspace/'lean-toolchain')
deps=sorted((retained/'.lake/packages').glob('*/.lake/build/lib/lean'))
env=dict(os.environ,PATH='/home/dombarker/.elan/bin:/usr/bin:/bin',NO_DNA='1',
    LEAN_PATH=':'.join(map(str,[cache,*deps,runtime/'.lake/build/lib/lean'])))
records=[];pins={};seen=set()
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
            for name in line.split('import ',1)[1].split():visit(name)
for item in manifest['targets']:
    src=sources/(item['target']+'.lean');assert sha(src)==item['sha256'],item['target']
    visit(item['target'].replace('/','.'))
(a.output/'dependency-pins.json').write_text(json.dumps(pins,indent=2)+'\n')
for item in manifest['targets']:
    name=item['target'];src=sources/(name+'.lean');obj=cache/(name+'.olean');obj.parent.mkdir(parents=True,exist_ok=True)
    cmd=['/home/dombarker/.elan/bin/lake','env','lean','-j1','-M4500','-R',str(sources),'-o',str(obj),str(src)]
    log=a.output/(Path(name).name+'.log')
    with log.open('w') as f:
        result=subprocess.run(['/usr/bin/time','-v',*cmd],cwd=workspace,env=env,stdout=f,stderr=subprocess.STDOUT)
    text=log.read_text();print(text,flush=True)
    records.append({'target':name,'sha256':item['sha256'],'exit':result.returncode,'command':cmd,
        'base_revision':manifest['base_revision'],'toolchain':(workspace/'lean-toolchain').read_text().strip()})
    if result.returncode or 'sorryAx' in text:raise SystemExit(result.returncode or 2)
for path,digest in pins.items():assert sha(Path(path))==digest,path
(a.output/'metadata.json').write_text(json.dumps(records,indent=2)+'\n')
(a.output/'manifest.json').write_text(json.dumps(manifest,indent=2)+'\n')
print(json.dumps({'status':'PASS','compiled':len(records),'dependency_pins':len(pins)}))
