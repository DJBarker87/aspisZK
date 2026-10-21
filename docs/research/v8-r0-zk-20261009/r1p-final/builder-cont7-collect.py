#!/usr/bin/env python3
"""Retain capped host receipts and source pins, without copying binary artifacts."""
import hashlib,json,pathlib,subprocess
HERE=pathlib.Path(__file__).resolve().parent
ROOT=HERE.parents[3]
script=r'''
import pathlib,json,hashlib,subprocess
R=pathlib.Path('/home/dombarker/project-offloads/codex-cx-builder-ref7-20261021')
def pin(p):return dict(sha256=hashlib.sha256(p.read_bytes()).hexdigest(),size=p.stat().st_size)
result={}
result['elf_cmp']={}
for mode,artifact in [('default','aspis_r1_cost_probe_program.so'),('devnet','aspis_r1_cost_probe_program.so'),('pool','aspis_pool.so')]:
 p=R/'stage0/artifacts'/mode/artifact
 q=pathlib.Path('/home/dombarker/project-offloads/codex-cx-builder-ref2-20261021/stage0/artifacts')/mode/artifact
 if p.exists():result['elf_cmp'][mode]=dict(exit=subprocess.run(['cmp','-s',str(p),str(q)]).returncode,current=pin(p),frozen=pin(q))
for group in ['nullifier','forest-owned-p6','forest-owned-match-p6','columns','stage0/receipts']:
 e=R/group
 rec={}
 for p in e.rglob('*'):
  if not p.is_file():continue
  if p.name=='receipt.json': rec[str(p.relative_to(R))]=json.loads(p.read_text())
  elif p.suffix in ['.log','.lean','.json','.llbc']:rec[str(p.relative_to(R))]=pin(p)
 result[group]=rec
old=(R/'stage0/src/tools/r1-builder-reference/nullifier.rs').read_text()
new=(R/'source/tools/r1-builder-reference/nullifier.rs').read_text()
def reference_prefix(s):
 s=s.split('#[cfg(kani)]\nmod proofs',1)[0]
 if '#[cfg_attr(kani, kani::ensures' in s:
  a=s.index('#[cfg_attr(kani, kani::ensures');b=s.index('pub fn preimage_owned',a)
  s=s[:a]+s[b:]
 return s
assert reference_prefix(old)==reference_prefix(new)
result['nullifier_cfg_independent_reference_identity']=dict(equal=True,
 initial_file=pin(R/'stage0/src/tools/r1-builder-reference/nullifier.rs'),
 current_file=pin(R/'source/tools/r1-builder-reference/nullifier.rs'),
 reference_body_sha256=hashlib.sha256(reference_prefix(new).encode()).hexdigest(),
 excluded='cfg(kani) proofs and cfg_attr(kani) contract metadata only; every reference function body unchanged')
result['source_pins']={}
for dirname in ['source','stage0/src']:
 base=R/dirname; pins={}
 for name in ['crates','programs','tools/r1-builder-reference','docs/research/v8-r0-zk-20261009/refine']:
  for p in (base/name).rglob('*'):
   if p.is_file() and p.suffix in ['.rs','.toml'] and 'target' not in p.parts:
    pins[str(p.relative_to(base))]=pin(p)
 result['source_pins'][dirname]=pins
for name in ['Cargo.toml','Cargo.lock']:
 p=R/'stage0/src'/name
 result['source_pins']['stage0/src'][name]=pin(p)
result['diagnostics']={}
for d in ['nullifier/kani','nullifier/kani-words','nullifier/kani-limbs','nullifier/aeneas','forest-owned-p6/aeneas','forest-owned-match-p6/aeneas','columns/aeneas-columns']:
 p=R/d/'stdout.log';q=R/d/'stderr.log'
 if p.exists(): result['diagnostics'][d]=p.read_text()[-14000:]+('\nSTDERR\n'+q.read_text()[-5000:] if q.exists() else '')
print(json.dumps(result))
'''
r=json.loads(subprocess.check_output(['ssh','dombarker@100.108.41.90','python3 -'],input=script,text=True))
for dirname,pins in r['source_pins'].items():
 matches={}; mismatches={}
 for name,pin in pins.items():
  p=ROOT/name
  if p.exists():
   actual=hashlib.sha256(p.read_bytes()).hexdigest()
   (matches if actual==pin['sha256'] else mismatches)[name]=actual
 r.setdefault('checkout_comparison',{})[dirname]=dict(matched=len(matches),mismatches=mismatches)
r['checkout_revision']=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip()
expected={k:v['artifact_sha256'] for k,v in json.loads((HERE/'builder-cont3-evidence/elf-rebuild-final.json').read_text()).items()}
elf={}
for mode,want in expected.items():
 key='stage0/receipts/'+mode+'/receipt.json'
 if key in r['stage0/receipts']:
  rec=r['stage0/receipts'][key];assert rec['exit_status']==0 and rec['artifact_sha256']==want
  elf[mode]=rec
r['frozen_elf_matches']=list(elf)
(HERE/'builder-cont7-host-evidence.json').write_text(json.dumps(r,indent=2)+'\n')
print('ELF matches:',list(elf),'comparisons:',r['checkout_comparison'])
