#!/usr/bin/env python3
"""Collect exact capped receipts, source pins and diagnostics, excluding binaries."""
import pathlib, subprocess, json, hashlib
HERE=pathlib.Path(__file__).resolve().parent
ROOT=HERE.parents[3]
script=r'''
import pathlib,hashlib,json,subprocess
R=pathlib.Path('/home/dombarker/project-offloads/codex-cx-builder-ref8-20261021')
def pin(p):return dict(sha256=hashlib.sha256(p.read_bytes()).hexdigest(),size=p.stat().st_size)
d={'receipts':{},'artifacts':{},'diagnostics':{},'source_pins':{},'elf_cmp':{}}
kit=pathlib.Path('/home/dombarker/project-offloads/aspis-r1-r18-tools-20261016')
paths=[kit/'charon-target/release/charon',kit/'bin/aeneas',pathlib.Path('/home/dombarker/.cargo/bin/cargo-kani')]
paths += [pathlib.Path('/home/dombarker/.kani/kani-0.67.0/bin')/n for n in ['cbmc','kani-compiler','goto-instrument']]
d['tools']={str(p):pin(p.resolve())|dict(resolved=str(p.resolve())) for p in paths if p.exists()}
d['cancellations']={str(p.relative_to(R)):json.loads(p.read_text()) for p in [R/'cancelled-literal.json',R/'carry/literal-stopped.json'] if p.exists()}

for group in ['tree','carry','step','projected','forest-tree-p6','stage0/receipts']:
 for p in (R/group).rglob('*'):
  if not p.is_file():continue
  key=str(p.relative_to(R))
  if p.name=='receipt.json' or p.name in ['stopped.json','tree-replacement.json','source-replacement.json']:
   d['receipts'][key]=json.loads(p.read_text())
  d['artifacts'][key]=pin(p)
  if p.name in ['stdout.log','stderr.log'] and group!='stage0/receipts':
   s=p.read_text(errors='replace')
   d['diagnostics'][key]=s[-18000:]
for base in ['source','projected-source','stage0/src']:
 pins={}
 for root in ['crates','programs','tools/r1-builder-reference','docs/research/v8-r0-zk-20261009/refine']:
  for p in (R/base/root).rglob('*'):
   if p.is_file() and p.suffix in ['.rs','.toml'] and 'target' not in p.parts:pins[str(p.relative_to(R/base))]=pin(p)
 for f in ['Cargo.toml','Cargo.lock']:
  if (R/base/f).exists():pins[f]=pin(R/base/f)
 d['source_pins'][base]=pins
for mode,name in [('default','aspis_r1_cost_probe_program.so'),('devnet','aspis_r1_cost_probe_program.so'),('pool','aspis_pool.so')]:
 p=R/'stage0/artifacts'/mode/name
 q=pathlib.Path('/home/dombarker/project-offloads/codex-cx-builder-ref2-20261021/stage0/artifacts')/mode/name
 d['elf_cmp'][mode]=dict(current=pin(p),frozen=pin(q),exit=subprocess.run(['cmp','-s',str(p),str(q)]).returncode)
print(json.dumps(d))
'''
r=json.loads(subprocess.check_output(['ssh','dombarker@100.108.41.90','python3 -'],input=script,text=True))
r['checkout_revision']=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip()
r['checkout_comparison']={}
for base,pins in r['source_pins'].items():
 mismatches={};matched=0
 for f,pin in pins.items():
  p=ROOT/f
  if p.exists():
   sha=hashlib.sha256(p.read_bytes()).hexdigest()
   if sha==pin['sha256']:matched+=1
   else:mismatches[f]=sha
 r['checkout_comparison'][base]=dict(matched=matched,mismatches=mismatches)
assert all(x['exit']==0 for x in r['elf_cmp'].values())
assert not {f:v for f,v in r['checkout_comparison']['stage0/src']['mismatches'].items() if f.startswith(('crates/','programs/'))}
assert 'tools/r1-builder-reference/tree.rs' not in r['checkout_comparison']['projected-source']['mismatches']
(HERE/'builder-cont8-host-evidence.json').write_text(json.dumps(r,indent=2)+'\n')
print('ELFs identical; source comparisons:',r['checkout_comparison'])
