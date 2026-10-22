"""Collect a continuation stage in the host workspace (no binaries/keys)."""
from pathlib import Path
import json,hashlib,re,statistics,sys,shutil
h=Path(sys.argv[1]);stage=sys.argv[2];r=h/('pr1-'+stage);out=Path(sys.argv[3]);out.mkdir(parents=True,exist_ok=True)
rows=[];identities=[]
for run in range(3):
 for j,f in enumerate(['transfer','withdrawal']):
  tag='repaired' if stage=='step2' else 'release'
  p=r/('fixtures-'+stage+'-'+tag)/f'S2-{f}-{run}'
  meta=json.loads((p/'fixture.json').read_text());assert meta['native_acceptance'] is True and meta['dense_acceptance'] is True
  times=[list(map(float,x.split())) for x in re.findall(r'^PR1_TIME (.*)$',(r/'receipts'/f'pr1-{stage}-fixtures-{tag}'/'stderr.log').read_text(),re.M)]
  assert len(times)==6 and all(len(t)==5 and t[4]>=sum(t[:4])for t in times)
  for file in ['proof.bin','public.bin']:
   a=(p/file).read_bytes();b=(h/'pr1-baseline/fixtures'/f'S2-{f}-0'/file).read_bytes();assert a==b
   identities.append(dict(fixture=f,run=run,file=file,sha256=hashlib.sha256(a).hexdigest(),bytes=len(a)))
  rows.append(dict(fixture=f,run=run,p_r1_seconds=times[2*run+j][4],phases_seconds=times[2*run+j][:4],end_to_end_seconds=meta['prover_wall_seconds'],native_acceptance=meta['native_acceptance'],dense_acceptance=meta['dense_acceptance']))
base=json.loads((h/'pr1-baseline/challenges.json').read_text());new=json.loads((r/f'challenges-{stage}{"-repaired" if stage=="step2" else "-release"}.json').read_text());assert len(new)==len(base)==1000
assert [(x['input_sha256'],x['accepted'])for x in base]==[(x['input_sha256'],x['accepted'])for x in new]
med={f:{k:statistics.median(x[k]for x in rows if x['fixture']==f)for k in ['p_r1_seconds','end_to_end_seconds']}for f in ['transfer','withdrawal']}
result=dict(stage=stage,measurement_only=True,samples=rows,medians=med,byte_identity=identities,challenge_count=len(new),challenge_accepts=sum(x['accepted']for x in new),challenge_mismatches=0,target_met=all(x['p_r1_seconds']<=10 and x['end_to_end_seconds']<15 for x in med.values()))
receipt=json.loads((r/'receipts'/f'pr1-{stage}-fixtures-{tag}'/'receipt.json').read_text())
result['resources']={k:receipt[k] for k in ['target','source_revision','deps_fingerprint','exit_status','wall_seconds','peak_rss_kib','swaps','cgroup_memory_peak_bytes','cgroup_swap_peak_bytes','limits','print_axioms','toolchain','cpu']}
result['resources']['sampled_thread_counts']=sorted({x['threads'] for x in receipt['thread_samples']})
result['resources']['tasksmax_raised']=False
result['host_binaries']={p.name:dict(sha256=hashlib.sha256(p.read_bytes()).hexdigest(),bytes=p.stat().st_size) for p in [r/'complete-bin',r/'challenge-bin']}
assert receipt['exit_status']==0
baseline=json.loads((h/'pr1-summary-complete/complete-summary.json').read_text())['measurements']['baseline']['medians']
result['baseline']=baseline
if stage=='step3':
 previous=json.loads((h/'pr1-continuation-step2/summary.json').read_text())['medians']
 result['previous_stage_medians']=previous
 result['gain_over_previous_on_both']=all(med[f][k]<previous[f][k] for f in med for k in med[f])
 result['stop_reason']='prescribed stop after stage 3' if not result['target_met'] else 'timing targets met'
result['gain_on_both']=all(med[f][k]<baseline[f][k] for f in med for k in med[f])
result['regression_over_10_percent']=any(med[f]['end_to_end_seconds']>baseline[f]['end_to_end_seconds']*1.1 for f in med)
(out/'summary.json').write_text(json.dumps(result,indent=2)+'\n')
for p in (r/'receipts').glob(f'*{stage}*/receipt.json'):
 shutil.copytree(p.parent,out/'receipts'/p.parent.name,dirs_exist_ok=True)
for p in r.glob(f'reservation-*{stage}*.json'):shutil.copyfile(p,out/p.name)
shutil.copyfile(r/f'challenges-{stage}{"-repaired" if stage=="step2" else "-release"}.json',out/'challenges.json')
for mode in ['default','devnet','pool']:
 assert json.loads((r/'receipts'/f'elf-pr1{stage}-{mode}'/'receipt.json').read_text())['exit_status']==0
elf=json.loads((r/'elf-identities.json').read_text());assert len(elf)==3 and all(x['exit_status']==0 and x['byte_equal'] and x['sha256']==x['expected_sha256'] for x in elf)
shutil.copyfile(r/'elf-identities.json',out/'elf-identities.json')
print(json.dumps(med,indent=2))
for file in ['source-revision.txt']:
 shutil.copyfile(r/file,out/file)
# The copied instrumentation is confined to the snapshots; retain its exact text.
for file in ['docs/research/v8-r0-zk-20261009/z4/z9e.rs','crates/aspis-r1-cost-probe/examples/ct_fixture_gate.rs','crates/aspis-r1-cost-probe/examples/pr1_challenges.rs']:
 shutil.copyfile(r/file,out/(Path(file).name+'.txt'))

shutil.copyfile(r/'Cargo.lock',out/'root-Cargo.lock.txt')

if stage=='step3':
 for file,outfile in [('step3-before-early-gate-z9c.rs.txt','before-early-gate-z9c.rs.txt'),('challenges-step3.json','before-early-gate-challenges-partial.json')]:
  shutil.copyfile(r/file,out/outfile)

if stage=='step3':
 for file,outfile in [('step3-serial-lift-z9c.rs.txt','serial-lift-z9c.rs.txt'),('challenges-step3-final.json','serial-lift-challenges-partial.json')]:
  shutil.copyfile(r/file,out/outfile)
