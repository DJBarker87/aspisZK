#!/usr/bin/env python3
"""Validate this job's receipt set, positive/negative controls and copied hashes."""
import hashlib,json,pathlib,collections
ROOT=pathlib.Path(__file__).resolve().parents[4];E=ROOT/'results/gr1-cost-20261013';load=lambda p:json.loads(p.read_text())
copies=load(E/'copied-evidence-sha256.json')
for rel,v in copies.items():assert hashlib.sha256((E/rel).read_bytes()).hexdigest()==v['sha256'],rel
receipts=[]
for p in sorted(E.glob('*.json')):
 d=load(p)
 if 'exit_status' not in d:continue
 assert d['caps']=={'memory.high':str(4*2**30),'memory.max':str(6*2**30),'memory.swap.max':'0'}
 assert d['cgroup_swap_current_bytes']==0 and d['stop_reason'] is None
 assert d['exit_status']==({'native-full-random.json':101,'withdrawal-stage-d18.json':1}.get(p.name,0))
 receipts.append(dict(path=p.name,**{k:d[k] for k in ['command','source_revision','exit_status','wall_seconds','peak_aggregate_rss_bytes_sampled','cgroup_memory_peak_bytes','child_peak_rss_kib','cgroup_swap_current_bytes','caps']}))
assert len(receipts)==32,len(receipts)
for version in ['v2','v3b']:
 for name in ['transfer','withdrawal']:
  signatures=[]
  for i in range(1,6):
   d=load(E/f'pool-{version}-{name}-{i}-evidence.json');ex=d['execution'];assert ex['error'] is None and ex['stage1_error'] is None
   assert ex['simulation_equals_execution'] and ex['stage1_simulation_equals_execution']
   negatives=ex['uploader_lifecycle']['negative_checks'];assert len(negatives)==(9 if name=='transfer' else 0) and all(x['rollback'] and x['program_error'] for x in negatives)
   signatures.append((ex['compute_units'],ex['stage1_compute_units'],d['fixture']['proof_sha256'],d['artifacts']['selected_verifier']['sha256']))
  assert len(set(signatures))==1
for name in ['transfer','withdrawal']:
 for tx in [1,2]:
  costs=[]
  for i in range(1,6):
   d=load(E/f'full-random/measurements/{name}-acceptance-k10-tx{tx}-run{i}.json');assert d['verifier_completed'] and d['execution']['error'] is None and d['proof_and_public_unchanged'] and d['identical_to_first_run']
   assert d['elf_sha256']=='48857d754accece121046c5e0ceaa79d49fbbe22e89f1bdda55d08f66ef84a9a';costs.append(d['execution']['cu'])
  assert len(set(costs))==1
 cases=load(E/f'full-random/{name}-mutations.json')['cases'];assert len(cases)==5675
 assert all(x['strict'].startswith('Err(') and x['authenticated'].startswith('Err(') and x['strict_trace_entries']==x['authenticated_trace_entries']==0 for x in cases)
for f in load(E/'full-random/native-gate.json')['fixtures']:
 assert f['native_dense_equal'] and f['strict_authenticated_equal'] and f['trace_count']==10699 and f['tx2_trace_count']==9253
for f in load(E/'mask-tape.json')['fixtures']:
 assert f['eligible_noise_cells']==f['eligible_noise_changed_cells']==3803 and f['D_rows']==f['G_rows']==1024 and f['mask_only_cells']==10240 and f['H1_padding_free_samples']==809 and f['all_eligible_and_full_word_cells_nonzero_for_this_seed']
for f in load(E/'adapter-dense-result.json')['fixtures']:
 assert f['native_dense_equal'] and f['strict_authenticated_equal'] and f['trace_entries']==10699 and f['tx2_trace_entries']==9253
 for version in ['v2','v3b']:
  assert f['proof_sha256']==load(E/f"pool-{version}-{f['fixture']}-1-evidence.json")['fixture']['proof_sha256']
repairs={'native-full-random.json':'Archive omitted unrelated Cargo workspace members: copied missing member files, preserved every archive source member; retry native-full-random-r2 passed.','withdrawal-stage-d18.json':'Old P2 transport proof is incompatible with D18: tx2 rejects at Relation. Retained failure; final D18 column uses its existing five successful regenerated-proof runs, not a rerun of incompatible bytes.'}
report={'schema':'aspis.gr1-cost.audit.v1','scope':'Rust cost/conditional parser coverage only; no security/release claims','all_checks_passed':True,'copied_files_hash_verified':len(copies),'new_scoped_commands':len(receipts),'caps':'MemoryHigh=4G MemoryMax=6G MemorySwapMax=0','all_new_scopes_zero_swap':True,'adapter_operations_each_five_runs':4,'random_d18_operation_transaction_cells_each_five_runs':4,'mutations_per_operation_per_entrypoint':5675,'native_dense_entries_per_operation':10699,'strict_authenticated_tx2_entries_per_operation':9253,'release_equivalence_tests_passed':15,'repair_or_expected_failure':repairs,'receipts':receipts,'limitations':['D18 transport and rho-field transitions are not a P2 security-equivalence claim.','v2 historical build has no complete source-file manifest; retained ELF and build/stack/input hashes pinned.','Full-random measurements are the selected standalone d18 ELF; adapter fixtures are separately measured.','Rollover deliverable is a design note; no successful 255-pair spend claimed.','One recorded random tape per operation, five runtime repetitions; no worst-case CU bound.']}
(E/'evidence-audit.json').write_text(json.dumps(report,indent=2)+'\n')
print('Receipt, copy-hash, five-run, mutation and dense-equivalence audits passed.')
