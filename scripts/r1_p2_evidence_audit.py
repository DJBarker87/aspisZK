#!/usr/bin/env python3
"""Check retained P2 evidence only; never execute a measurement."""
import hashlib,json,subprocess
from pathlib import Path
root=Path(__file__).resolve().parent.parent
r=root/'results/r1-precheck-20261010'
read=lambda p:json.loads(p.read_text())
sha=lambda b:hashlib.sha256(b).hexdigest()
art=read(r/'build-host-artifacts.json')
artifacts={x['path'].split('/results/r1-precheck-20261010/')[1]:x for x in art['artifacts']}
assert len(artifacts)==len(art['artifacts'])
resources=[]
for p in r.glob('*.json'):
 d=read(p)
 if 'caps' not in d:continue
 assert d['caps']=={'memory.high':'4294967296','memory.max':'6442450944','memory.swap.max':'0'},p
 assert d['cgroup_swap_current_bytes']==0 and d['stop_reason'] is None,p
 assert d['peak_aggregate_rss_bytes_sampled']<6442450944,p
 resources.append((p.name,d))
configs=[];diag_count=acceptance_count=0;peak_heap=0
for v in ['S1','S2','D']:
 a=read(r/v/'stack-audit/stack-audit.json')
 assert not a['reachable_diagnostics']
 assert a['all_diagnostic_functions_absent_from_linked_elf']
 assert a['text_sha256']['linked']==a['text_sha256']['measured']
 assert a['linked_sha256']==artifacts[f'{v}/bin/aspis_r1_cost_probe_program-unstripped.so']['sha256']
 assert a['measured_elf_sha256']==artifacts[f'{v}/bin/aspis_r1_cost_probe_program.so']['sha256']
 for name in ['linked','measured']:
  assert a['text_sha256'][name]==artifacts[f'{v}/stack-audit/{name}.text']['sha256']
 native=read(r/v/'native-gate.json')
 for d in native['fixtures']:
  assert all(d[k] for k in ['native_acceptance','dense_acceptance','all_challenge_weight_check_bytes_equal','checkpoint_roundtrip'])
  m=read(r/v/(d['fixture']+'-mutations.json'))
  assert len(m['cases'])==m['count']==d['mutations_rejected']>=200
  assert all(x['error'] for x in m['cases'])
  assert any(x['case'].startswith('checkpoint') for x in m['cases'])
  assert d['proof_bytes']==artifacts[f"{v}/fixtures/{d['fixture']}.proof.bin"]['size_bytes']
 k=read(r/v/'balance-selection.json')['selected']['k']
 for p in (r/v/'measurements').glob('*-tx*-run*.json'):
  d=read(p)
  assert d['elf_sha256']==a['measured_elf_sha256'],p
  assert d['proof_sha256']==artifacts[f"{v}/fixtures/{d['fixture']}.proof.bin"]['sha256'],p
  assert d['proof_and_public_unchanged'],p
  if '-diagnostic-' in p.name:
   diag_count+=1
   assert d['verifier_completed'] and d['execution']['error'] is None,p
   assert d['sbf_heap_high_water_bytes']<=262144,p
   peak_heap=max(peak_heap,d['sbf_heap_high_water_bytes'])
   assert d['execution']['cu']-d['verifier_cu']==356,p
  else:
   acceptance_count+=1
   assert d['runtime']['limit_cu']==1400000,p
   assert not d['verifier_completed'] and d['execution']['error']=='InstructionError(2, ProgramFailedToComplete)',p
   assert any('exceeded CUs meter at BPF instruction' in s for s in d['execution']['logs']),p
 for f in ['transfer','withdrawal']:
  for tx in [1,2]:assert len(list((r/v/'measurements').glob(f'{f}-acceptance-k{k}-tx{tx}-run*.json')))==5
 configs.append(dict(variant=v,k=k,fixtures=native['fixtures'],reachable_stack_diagnostics=0,retained_functions=a['linked_function_count']))
table=read(r/'cumulative-table.json')
phase_keys=['Parse','Semantic','Prepare','Checkpoint read','Merkle','Query folds and rho accumulation','Relation rounds and pairing','Final rho evaluation','Checkpoint write','Entry/exit and other overhead']
for d in table['records']:
 assert sum(d[k] for k in phase_keys)==d['Program subtotal CU']
 assert d['Program subtotal CU']+d['Other transaction overhead CU']==d['Total transaction CU']
 assert d['Headroom to 1,300,000']==1300000-d['Total transaction CU']
 assert d['Acceptance at 1,400,000']=='0/5'
# Exact historical sources are content-addressed; do not rerun their builds.
replay=read(r/'source-replay.json')
for stage in replay['stages']:
 p=r/stage['source_manifest'];assert sha(p.read_bytes())==stage['source_manifest_sha256']
 for name,expected in read(p)['files'].items():
  b=(replay['utf8_blobs_by_sha256'][expected].encode() if name in stage['exact_file_overrides'] else (root/name).read_bytes())
  assert sha(b)==expected,(stage['stage'],name)
# A whitelist also excludes all reference and Lean paths, including untracked additions.
changed=subprocess.check_output(['git','diff','--name-only','600eb0138'],cwd=root,text=True).splitlines()
changed+=subprocess.check_output(['git','ls-files','--others','--exclude-standard'],cwd=root,text=True).splitlines()
allowed=lambda p:p in ['Cargo.toml','Cargo.lock'] or p.startswith(('crates/aspis-r1-cost-probe/','programs/r1-cost-probe/','tools/r1-cost-probe/','results/r1-precheck-20261010/','scripts/r1_p2_'))
assert all(allowed(p) for p in changed),[p for p in changed if not allowed(p)]
assert all(p.suffix in ['.json','.md','.log'] for p in r.rglob('*') if p.is_file())
assert not any('keypair' in p.name or 'payer' in p.name for p in r.rglob('*'))
record=dict(label='UNPROVED R1 COST PROBE; retained-evidence audit only',base='600eb013878a0169cdab8f222e879cd395e3a1e2',configs=configs,resource_scopes=len(resources),peak_sampled_aggregate_rss_bytes=max(d['peak_aggregate_rss_bytes_sampled'] for _,d in resources),peak_cgroup_memory_bytes=max(d['cgroup_memory_peak_bytes'] for _,d in resources),swap_bytes=0,compile_only_failures=[n for n,d in resources if d['exit_status']!=0],completed_diagnostic_transactions=diag_count,capped_acceptance_attempts=acceptance_count,capped_acceptances=0,largest_completed_heap_bytes=peak_heap,phase_sums_reconcile=True,exact_historical_source_stages=len(replay['stages']),reference_and_lean_paths_unchanged=True,evidence_extensions=['json','md','log'],retained_binary_artifact_count=len(artifacts),retained_binary_artifact_bytes=sum(x['size_bytes'] for x in artifacts.values()),artifact_retention_requirement_met=False,retention_gap=art['retention_gap'],unchanged_measurements_rerun=False)
(r/'evidence-audit.json').write_text(json.dumps(record,indent=2)+'\n')
print(json.dumps({k:v for k,v in record.items() if k not in ['configs','retention_gap']}))
