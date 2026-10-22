#!/usr/bin/env python3
"""Promote only generated text; retain extraction pins, never binary artifacts."""
import subprocess, json, hashlib
from pathlib import Path
E=Path(__file__).resolve().parent.parent
H='/home/dombarker/project-offloads/codex-cx-prover-commit17-20261021'
host='dombarker@100.108.41.90'
L=Path('docs/research/v8-r0-zk-20261009/lean/AspisR1ProverAssembly17')
L.mkdir(exist_ok=True)
raw=E/'extraction';raw.mkdir(exist_ok=True)
pins=[]
for name in ['Types','Funs']:
 p=raw/(name+'.lean.txt')
 subprocess.run(['scp',host+':'+H+'/extraction/generated-v1/AspisR1ProverAssembly17/'+name+'.lean',str(p)],check=True)
 s=p.read_text();assert s.count('import Aeneas\n')==1
 s=s.replace('import Aeneas\n','import Aeneas.Std\nimport Aeneas.Tactic.RustAttributes\nimport Aeneas.Data.Discriminant\n')
 if name=='Types':
  assert s.count('@[discriminant isize]')==1
  s=s.replace('@[discriminant isize]\n','')
  previous=Path('docs/research/v8-r0-zk-20261009/lean/AspisR1ProverMaterial14/Types.lean').read_text()
  start=previous.index('-- Explicit discriminant instance')
  end=previous.index('end AspisR1ProverMaterial14',start)
  adapter=previous[start:end].replace('instMaterial14MaskErrorDiscriminant','instAssembly17MaskErrorDiscriminant')
  s=s.replace('end AspisR1ProverAssembly17',adapter+'end AspisR1ProverAssembly17')

 (L/(name+'.lean')).write_text(s)
 pins.append(dict(module='AspisR1ProverAssembly17.'+name,raw_sha256=hashlib.sha256(p.read_bytes()).hexdigest(),promoted_sha256=hashlib.sha256((L/(name+'.lean')).read_bytes()).hexdigest(),edit='Replace root Aeneas import with existing Std + RustAttributes + Data.Discriminant (narrow-import compatibility); replace unsupported generated discriminant attribute by the existing Material14 explicit five-constructor discriminant instance. Generated resource options unchanged.'))
for name in ['assembly-charon-v1','assembly-aeneas-v1']:
 d=E/'receipts'/name;d.mkdir(exist_ok=True,parents=True)
 for f in ['receipt.json','stdout.log','stderr.log','time.log']:
  subprocess.run(['scp',host+':'+H+'/receipts/'+name+'/'+f,str(d/f)],check=True)
 subprocess.run(['scp',host+':'+H+'/'+name+'-inputs.json',str(E/(name+'-inputs.json'))],check=True)
for source,dest in [('assembly-llbc-v1.json','llbc.json'),('src/crates/aspis-prover/src/prover_commit_reference.rs','reference-with-assembly.rs')]:
 subprocess.run(['scp',host+':'+H+'/'+source,str(raw/dest)],check=True)
(raw/'promotion.json').write_text(json.dumps(pins,indent=2)+'\n')
