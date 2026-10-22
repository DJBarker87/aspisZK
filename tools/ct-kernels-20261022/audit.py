#!/usr/bin/env python3
from pathlib import Path
import json,hashlib,subprocess,re
R=Path(__file__).resolve().parents[2];E=R/'docs/research/100bit-spend-path-20261013/evidence/ct-kernels-20261022'
accepted=['kani-base-traces-final','kani-final','kani-tower-traces-v1','kani-mixed-traces','kani-canonical-closure-v2','kani-raw-constructors','kani-parametric-cm-v1','kani-parametric-cm_square','kani-parametric-cm_mul_m31']+['kani-parametric-v3-'+n for n in ['qm_mul','qm_square','qm_mul_m31','qm_mul_cm31','wide_mul','wide_square','wide_mul_m31','wide_mul_qm31']]
rows=[];count=0;harnesses=set()
for folder in ['receipts','baseline-receipts','control-receipts']:
 for p in sorted((E/folder).glob('*/receipt.json')):
  r=json.loads(p.read_text());out=(p.parent/'stdout.log').read_text();name=p.parent.name
  summary={k:r.get(k) for k in ['attempt','target','source_revision','deps_fingerprint','exit_status','wall_seconds','peak_rss_kib','swaps','cgroup_memory_peak_bytes','cgroup_swap_peak_bytes','limits','print_axioms','expected_work']};summary['receipt']=str(p.relative_to(E));summary['artifact_status']=('accepted rebuilt candidate' if name.startswith('elf-v5-') else 'invalidated stale-cache control' if name=='frozen-control-elf-default' else 'fresh frozen-source control' if name=='frozen-control-elf-default-v2' else 'diagnostic or superseded artifact attempt' if 'elf' in name else 'not an ELF gate');summary['accepted_kani']=folder=='receipts' and name in accepted
  if summary['accepted_kani']:
   assert r['exit_status']==0,name
   m=re.search(r'Complete - (\d+) successfully verified harnesses, 0 failures, (\d+) total',out);assert m,name
   assert m[1]==m[2];count+=int(m[1]);harnesses.update(re.findall(r'Checking harness ([^\s]+)\.\.\.',out))
  assert r['limits']=={'memory.high':str(6*2**30),'memory.max':str(8*2**30),'memory.swap.max':'0','pids.max':'64'}
  assert r['swaps']==0
  rows.append(summary)
assert len(harnesses)==69,(len(harnesses),count)
assert set(accepted)<={r['attempt'] for r in rows if r['accepted_kani']}
elf=json.loads((E/'elf-identities.json').read_text());baseline=json.loads((E/'baseline-identities.json').read_text())
assert all(r['exit_status']==0 for r in elf)
assert all(r['byte_equal'] for r in baseline)
assert [r['mode'] for r in elf if r['byte_equal']]==['pool']
control=json.loads((E/'cache-control.json').read_text());assert control['byte_equal_frozen']
env=json.loads((E/'environment.json').read_text());assert not next(v for k,v in env['tls_symbols'].items() if k.endswith('timed-ct'))
fixture=json.loads((E/'fixture-identities.json').read_text());a,b=fixture
measure=[]
for name in ['S2-transfer','S2-withdrawal']:
 assert a['files'][name+'/proof.bin']==b['files'][name+'/proof.bin']
 x=json.loads((E/'fixtures-baseline'/name/'fixture.json').read_text());y=json.loads((E/'fixtures-ct'/name/'fixture.json').read_text())
 assert x['proof_bytes']==y['proof_bytes']==57607
 measure.append(dict(fixture=name,baseline_prover_seconds=x['prover_wall_seconds'],ct_prover_seconds=y['prover_wall_seconds'],change_percent=100*(y['prover_wall_seconds']/x['prover_wall_seconds']-1),classification='single fixture measurement including P_R1, not proof or L3 evidence'))
inputs={}
for base in ['crates/aspis-core','crates/aspis-prover','crates/aspis-r1-cost-probe','crates/aspis-statement','programs/r1-cost-probe','programs/aspis-pool','tools/ct-kernels-20261022','docs/research/v8-r0-zk-20261009/z4','docs/research/v8-r0-zk-20261009/c3']:
 for p in (R/base).rglob('*'):
  if p.is_file() and 'target' not in p.parts:inputs[str(p.relative_to(R))]=dict(sha256=hashlib.sha256(p.read_bytes()).hexdigest(),bytes=p.stat().st_size)
for name in ['Cargo.toml','Cargo.lock','results/r0-opening-20261009/kats.json','results/r0-opening-20261009/transport-kat.json','results/r0-codes-20261009/kats.txt','results/r0-samplers-20261009/kats.json']:
 p=R/name;inputs[name]=dict(sha256=hashlib.sha256(p.read_bytes()).hexdigest(),bytes=p.stat().st_size)
(E/'candidate-inputs.json').write_text(json.dumps(inputs,indent=2,sort_keys=True)+'\n')
(E/'gates.json').write_text(json.dumps(dict(adoption='blocked: baseline verifier drift from two frozen pins',accepted_symbolic_harnesses=len(harnesses),successful_harness_executions=count,accepted_harness_names=sorted(harnesses),attempts=rows,elf=elf,baseline_comparison=baseline,frozen_source_control=control,fixture_measurements=measure),indent=2)+'\n')
print(json.dumps(dict(symbolic_harnesses=len(harnesses),attempts=len(rows),adoption='blocked',fixture_measurements=measure)))
