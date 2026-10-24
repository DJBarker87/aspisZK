"""One focused final read-only source/MIR/evidence audit; no compiler invocation."""
from pathlib import Path
import json,hashlib,runpy,subprocess
D=Path(__file__).resolve().parent;ROOT=D.parents[2]
E=ROOT/'docs/research/100bit-spend-path-20261013/evidence/prover-rw-20261023/resume-mir'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
j=json.loads((E/'association.json').read_text());assert j==runpy.run_path(str(D/'inspect.py'))['inspect']();assert not j['native_projection']
c=json.loads((E/'collection.json').read_text())
assert len(c['selected'])==132
for x in c['selected']:
 p=E/'mir'/x['name'];assert p.stat().st_size==x['size'] and sha(p)==x['sha256']
s=json.loads((E/'source-identity.json').read_text())
for p,v in s['identical_copies'].items():assert sha(ROOT/p)==v['sha256']==sha(ROOT/v['source'])
for p,v in s['inspected_rule_inputs'].items():assert sha(ROOT/p)==v
pins=json.loads((E/'pin-summary.json').read_text());r=pins['receipt'];pre=pins['preflight']
assert pins['all_pre_go_post_equal'] and r['pins_unchanged'] and r['actual_invocations']==1 and r['exit_status']==0
assert r['command']==pre['command'] and r['source_revision']==(D/'revision.txt').read_text().strip()
assert pre['environment']['CARGO_BUILD_JOBS']=='1'
assert '-Zdump-mir=all' in pre['environment']['RUSTFLAGS'] and '--cfg prover_rw_resume_scalar' in pre['environment']['RUSTFLAGS'] and '--cfg kani' not in pre['environment']['RUSTFLAGS']
assert pre['command'][pre['command'].index('-j')+1]=='1' and '--release' in pre['command']
stage='/home/dombarker/project-offloads/codex-cx-prover-rw-20261023/resume-mir/'
ident=json.loads((E/'package-identity.json').read_text());vendor={f'vendor/{x["package"]}/{k}':v for x in ident for k,v in x['job_files'].items()}
for p,h in pins['source_and_dependencies'].items():
 if p.startswith(stage):
  rel=p[len(stage):]
  if rel.startswith('vendor/'):assert vendor[rel]==h
  elif rel=='package-identity.json':assert sha(E/rel)==h
  else:assert sha(D/rel)==h,(rel,h)
for name,request in [('readonly/diagnostic.json',2**30),('rust001/admission-before.json',2**30),('rust001/admission-barrier.json',0)]:
 a=json.loads((E/name).read_text());assert a['allowed'] and a['requested_bytes']==request
 assert a['projected_reserved_bytes']<55*2**30
 assert a['projected_reserved_bytes']+a['uncapped_resident_reserve_bytes']+7*2**30<a['meminfo']['MemTotal']
 assert a['meminfo']['MemAvailable']>request+2*2**30
 assert a['process_visibility'] and a['service_visibility'] and 'docker_visibility' in a
resources=json.loads((E/'rust001/resources.json').read_text())
assert resources['limits']==dict(zip(['memory.high','memory.max','memory.swap.max','pids.max'],map(str,[768*2**20,2**30,0,64])))
assert resources['peak_swap_bytes']==0 and r['swaps']==0
assert resources['cgroup_memory_peak_bytes']<=2**30
changed=subprocess.check_output(['git','diff','--name-only','f033f68bf75dcc2d0f03a5f5149eb557b6b4f609'],cwd=ROOT,text=True).splitlines()
assert all('/resume-mir/' in p for p in changed)
for p in [*D.rglob('*'),*E.rglob('*')]:
 if p.is_file():
  assert p.suffix not in ['.olean','.o','.rlib','.rmeta','.elf','.pyc'],p
  if p.suffix=='.json':assert p.stat().st_size<=5_000_000,p
assert not (D/'target').exists()
print(json.dumps(dict(schema='ProverRwResumeMIR-focused-audit-v1',result='PASS: current source/MIR role packet and focused compile pins; native projection NOT established',source_revision=subprocess.check_output(['git','rev-parse','HEAD'],cwd=ROOT,text=True).strip(),source_and_dependency_hashes={str(p.relative_to(ROOT)):sha(p) for p in sorted([p for p in D.rglob('*') if p.is_file()]+[p for p in E.rglob('*') if p.is_file() and p.name not in ['audit.stdout','audit.time','audit-receipt.json']])},full_axioms='N/A: no new Lean declarations/imports or axioms audit',new_validation=dict(cargo_rustc_builds=1,Kani=0,Lean=0,extraction=0,backend=0,ELF=0),budgets=dict(Rust='2/3 conservative charge; actual ordinary build1',Lean='240/260',Kani='59/60 final1 RESERVED',extraction='54/56',backend='15/16',ELF='0/3')),indent=2))
