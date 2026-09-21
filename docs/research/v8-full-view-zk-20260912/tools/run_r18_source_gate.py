#!/usr/bin/env python3
"""Run in a bounded Linux scope. Optimized actual-source witness gates.

Both fresh witness worlds use the same SHA transcript and source q22 sampler.
This is fixed-prefix evidence, not a distribution or full-privacy theorem.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path
import subprocess
import shutil

EXPERIMENTS=Path('docs/research/v8-no-work-100-20260907/experiments')
p=argparse.ArgumentParser(description=__doc__)
p.add_argument('--stage',type=Path,required=True)
p.add_argument('--output',type=Path,required=True)
p.add_argument('--world',type=int,choices=[0,1],help='focused replay of one changed/missing world')
a=p.parse_args()
root=a.stage.resolve()
assert not a.output.exists(), 'fresh evidence directory required'
meta=json.loads((root/'r18-stage.json').read_text())
assert meta['profile'] in ['AV8/R18/sparse-coded-G128-step3/two-channel/research-v1',
    'AV8/R18/sparse-coded-G128-step3/minimal-T163/research-v2']
for name,expected in meta['files'].items():
    assert hashlib.sha256((root/name).read_bytes()).hexdigest()==expected,name
host=json.loads((root/'r17-stage.json').read_text())
env=dict(os.environ)
for key in ['ASPIS_V8_MAX_FRONTIER_SCAN','ASPIS_V8_LIVE_CONTEXT','ASPIS_V8_COMPLETE_CONTEXT',
            'ASPIS_R15_ORACLE_TABLE','ASPIS_R17_COUPLED_AUDIT','ASPIS_R17_H1_SEMANTIC_AUDIT']:
    env.pop(key,None)
env.update(PATH='/home/dombarker/.cargo/bin:/usr/bin:/bin',NO_DNA='1',
    ASPIS_V8_POSITIVE_CASE='honest',RUSTFLAGS=host['rustflags'],
    CARGO_TARGET_DIR='/home/dombarker/project-offloads/aspis-v8-performance-20260908.scS2Jz/docs/research/v8-no-work-100-20260907/experiments/performance-host/target')
a.output.mkdir()
cmd=['/home/dombarker/.cargo/bin/cargo','build','--offline','--locked','--release','--jobs','2',
     '--features',host['features'],'--manifest-path',str(root/EXPERIMENTS/'performance-host/Cargo.toml'),
     '--bin','aspis-v8-performance-host']
print('R18 phase=compile optimized=true source='+meta['source_revision'],flush=True)
with (a.output/'compile.log').open('w') as log:
    subprocess.run(['/usr/bin/time','-v']+cmd,env=env,cwd=root,stdout=log,stderr=subprocess.STDOUT,check=True)
binary=(a.output/'aspis-r18-source-gate-host').resolve()
shutil.copy2(Path(env['CARGO_TARGET_DIR'])/'release/aspis-v8-performance-host',binary)
worlds=[0,1] if a.world is None else [a.world]
for world in worlds:
    fixture=(a.output/f'fixture-world{world}').resolve()
    print(f'R18 phase=source-proof-and-C1-H1-G-affine-elimination world={world} release=true',flush=True)
    env.pop('ASPIS_R15_SELECTED_SECOND',None)
    env.update(ASPIS_R16_SELECTED_SECOND=str(world),ASPIS_R17_C1_WITNESS_AUDIT='1')
    with (a.output/f'world{world}.log').open('w') as log:
        subprocess.run(['/usr/bin/time','-v',str(binary),str(fixture)],env=env,cwd=root,stdout=log,stderr=subprocess.STDOUT,check=True)
    env.pop('ASPIS_R17_C1_WITNESS_AUDIT')
    with (a.output/f'public-prefix-world{world}.log').open('w') as log:
        subprocess.run(['/usr/bin/time','-v',str(binary),'--audit-existing',str(fixture)],env=env,cwd=root,stdout=log,stderr=subprocess.STDOUT,check=True)
    text=(a.output/f'world{world}.log').read_text()
    for marker in ['R17_C1_WITNESS_VALIDATED','R17_G_WITNESS_JOINT equations=625 rank=601',
                   'R17_H1_WITNESS_JOINT rank=540','R17_CONTROL semantic_rounds=10 final_values=512']:
        assert marker in text, marker
    assert 'R17_PUBLIC_PREFIX_ACCEPTED' in (a.output/f'public-prefix-world{world}.log').read_text()
if len(worlds)==2:
    def prefix(world):
        return next(line for line in (a.output/f'public-prefix-world{world}.log').read_text().splitlines()
                    if line.startswith('R17_PUBLIC_PREFIX {'))
    assert prefix(0)!=prefix(1),'fixture worlds must give distinct accepted prefixes'
print(f'R18 source_worlds={worlds} original_affine_equations_passed=true full_privacy_proved=false',flush=True)
