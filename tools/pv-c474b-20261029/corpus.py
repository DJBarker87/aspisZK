"""Fresh combined-candidate execution of 1000 cases, coins 6000–6999; retained verified baseline corpus read-only.
Same Rust harness and comparator. Bounded asynchronous process scheduling only.
Maximum three prover processes total. Both source variants can use 16-worker
P_R1 teams (some phases have 16 workers plus the calling thread). Three
processes plus runner/controller/comparators fit TasksMax=64. Task-limit
rejections invalidate the entire cohort rather than becoming prover results.
"""
from pathlib import Path
import asyncio,json,hashlib,sys,time,os
H=Path('/home/dombarker/project-offloads/codex-pv-c474-20261029');O=H/'bundle/corpus-6000'
B={'baseline':Path('/home/dombarker/project-offloads/codex-pv-gate6-20261028/combined/baseline/bin/prover_rw_differential'), 'candidate':H/'native-target/client/pv-c474-differential'}
# Verify each baseline file against the previous committed evidence before reuse.
manifest=json.loads((H/'corpus-ledger-audit.json').read_text());assert manifest['passed'] and manifest['physical_ledger_pairs']==1000
for row in manifest['rows']:
 coin=row['coin'];p=H/'corpus-6000'/f'{coin}-baseline'/str(coin);pins=row['sides']['baseline']
 for name,key in [('public.bin','public_sha256'),('result.json','result_sha256'),('proof.bin','proof_sha256')]:
  assert (hashlib.sha256((p/name).read_bytes()).hexdigest() if (p/name).exists() else None)==pins[key],(coin,name)
 # Oracle streams are also covered by prior comparison hashes, not inferred.
 comparison=json.loads((H/'corpus-6000'/f'comparison-{coin}.json').read_text())
 for name,entry in comparison['comparisons'][0]['files'].items():
  assert hashlib.sha256((p/name).read_bytes()).hexdigest()==entry['baseline_sha256']
(O.parent/'baseline-corpus-reuse.json').write_text(json.dumps(dict(verified_cases=1000,manifest_sha256=hashlib.sha256((H/'corpus-ledger-audit.json').read_bytes()).hexdigest(),reason='Unchanged shipped baseline controls reused read-only; only combined candidate re-executed. Public/proof/result/ledger/oracle bytes compared by the unchanged full-file comparator.'),indent=2)+'\n')
assert not O.exists(), 'Never duplicate an existing corpus'
O.mkdir()
pin=json.loads(Path('/home/dombarker/project-offloads/codex-pv-gate6-20261028/combined/baseline/build-differential/binary-pins.json').read_text())['prover_rw_differential']
assert hashlib.sha256(B['baseline'].read_bytes()).hexdigest()==pin['sha256'] and B['baseline'].stat().st_size==pin['bytes']
slots=asyncio.Semaphore(3)
sems={k:slots for k in ['baseline','candidate']}
active=set();results={};start=time.monotonic()
(H/'bundle/corpus-pipeline-binaries.json').write_text(json.dumps({k:dict(sha256=hashlib.sha256(p.read_bytes()).hexdigest(),bytes=p.stat().st_size) for k,p in B.items()},indent=2)+'\n')
def resources():
 cg=Path('/sys/fs/cgroup'+Path('/proc/self/cgroup').read_text().split('0::')[1].strip())
 def number(name):return int((cg/name).read_text()) if (cg/name).exists() else None
 return dict(cgroup=str(cg),memory_current_bytes=number('memory.current'),memory_peak_bytes=number('memory.peak'),swap_current_bytes=number('memory.swap.current'),swap_peak_bytes=number('memory.swap.peak'),pids_current=number('pids.current'),pids_peak=number('pids.peak'),pids_events=dict((k,int(v)) for k,v in (line.split() for line in (cg/'pids.events').read_text().splitlines())),memory_events=dict((k,int(v)) for k,v in (line.split() for line in (cg/'memory.events').read_text().splitlines())))
def check_resources():
 r=resources()
 assert r['pids_events'].get('max',0)==0,dict(error='Task-limit pressure invalidates this cohort',resources=r)
 assert r['memory_events'].get('oom_kill',0)==0,r
 return r
def summary():
 rows=[results[k] for k in sorted(results)]
 return dict(required_pairs=1000,completed_pairs=len(rows),passed=all(r['passed'] for r in rows),complete=len(rows)==1000,fully_executed_proof_pairs=sum(r['fully_executed_proof_pairs'] for r in rows),rejected_prefix_pairs=sum(r['rejected_prefix_pairs'] for r in rows),oracle_logged_pairs=sum(r['oracle_logged_pairs'] for r in rows),elapsed_pipeline_seconds=time.monotonic()-start,concurrency=dict(total_prover_processes=3),harness='crates/aspis-r1-cost-probe/examples/prover_rw_differential.rs',comparator='tools/prover-rw-20261023/compare-corpus.py',cases=rows)
async def execute(cmd,log):
 with log.open('wb') as f:
  p=await asyncio.create_subprocess_exec(*map(str,cmd),stdout=f,stderr=asyncio.subprocess.STDOUT);active.add(p)
  try:
   code=await asyncio.wait_for(p.wait(),600)
   if code:raise RuntimeError(f'{cmd[0]} exited {code}: {log}')
  finally:active.discard(p)
async def side(coin,who):
 if who=='baseline':return
 legacy='baseline' if who=='baseline' else 'candidate';out=O/f'{coin}-{legacy}'
 if (out/str(coin)/'result.json').exists():return
 assert not out.exists(),f'Incomplete existing case: {out}'
 async with sems[who]:
  await execute([B[who],out,coin,1,1 if coin in {6006,6007,6010,6011} else 0],O/f'run-{coin}-{legacy}.log')
async def pair(coin):
 comparison=O/f'comparison-{coin}.json'
 if not comparison.exists():
  await asyncio.gather(side(coin,'baseline'),side(coin,'candidate'))
  await execute(['python3',H/'compare-corpus.py',H/'corpus-6000'/f'{coin}-baseline',O/f'{coin}-candidate',comparison],O/f'compare-{coin}.log')
 r=json.loads(comparison.read_text());assert r['passed'] and r['paired_runs']==1,r
 check_resources()
 results[coin]=dict(coin=coin,**{k:v for k,v in r.items() if k!='comparisons'})
 s=summary();(O/'pipeline-progress.json').write_text(json.dumps(s,indent=2)+'\n')
 print('PIPELINE_PROGRESS',json.dumps({k:s[k] for k in ['completed_pairs','passed','complete','fully_executed_proof_pairs','rejected_prefix_pairs']}),flush=True)
async def review():
 while True:
  await asyncio.sleep(600)
  cg=Path('/sys/fs/cgroup'+Path('/proc/self/cgroup').read_text().split('0::')[1].strip())
  row=dict(utc=time.time(),completed_pairs=len(results),memory_current_bytes=int((cg/'memory.current').read_text()),memory_peak_bytes=int((cg/'memory.peak').read_text()),pids_current=int((cg/'pids.current').read_text()),memory_swap_current_bytes=int((cg/'memory.swap.current').read_text()),decision='Same optimized full retry-owner P_R1 gate; cases continue to complete. Original cap retained, no increase.')
  with (O/'pipeline-resource-reviews.jsonl').open('a') as f:f.write(json.dumps(row)+'\n')
  print('RESOURCE_REVIEW',json.dumps(row),flush=True)
async def main():
 rev=asyncio.create_task(review())
 tasks=[asyncio.create_task(pair(c)) for c in range(6000,7000)]
 try:
  await asyncio.gather(*tasks)
  s=summary();s['final_resources']=check_resources();assert s['complete'] and s['completed_pairs']==1000 and s['fully_executed_proof_pairs']==600 and s['rejected_prefix_pairs']==100 and s['oracle_logged_pairs']==4
  (O/'pipeline-final.json').write_text(json.dumps(s,indent=2)+'\n')
 except BaseException as e:
  (O/'pipeline-failure.json').write_text(json.dumps(dict(error=repr(e),summary=summary()),indent=2)+'\n')
  for t in tasks:t.cancel()
  for p in list(active):
   if p.returncode is None:p.terminate()
  await asyncio.gather(*(p.wait() for p in list(active)),return_exceptions=True)
  raise
 finally:
  rev.cancel()
  (O/'pipeline-resources-final.json').write_text(json.dumps(resources(),indent=2)+'\n')
asyncio.set_child_watcher(asyncio.PidfdChildWatcher())
asyncio.run(main())
