#!/usr/bin/env python3
"""Collect text/JSON receipts only; never download binaries or LLBC files."""
import hashlib,json,pathlib,subprocess
HERE=pathlib.Path(__file__).resolve().parent
HOST='dombarker@100.108.41.90'
R='/home/dombarker/project-offloads/codex-cx-builder-ref2-20261021'
script='''import pathlib,json,hashlib,re
R=pathlib.Path(RR)
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
def metrics(p):
 s=p.read_text()
 def g(k):
  m=re.search(k,s); return m.group(1).strip() if m else None
 sig=g(r'Command terminated by signal ([0-9]+)')
 return dict(exit=str(128+int(sig)) if sig else g(r'Exit status: ([0-9]+)'),terminated_by_signal=sig,peak_rss_complete=not bool(sig), wall=g(r'Elapsed \\(wall clock\\) time \\(h:mm:ss or m:ss\\): (.+)'),peak_rss_kib=g(r'Maximum resident set size \\(kbytes\\): (\\d+)'),swaps=g(r'Swaps: (\\d+)'),time_log=s)
out={}
for name in ['attempt-helper1','attempt-status2','evidence-validator','evidence-transport','evidence-compiler']:
 d=R/name
 if not (d/'charon.log').exists(): continue
 rec={}
 for tool in ['charon','aeneas']:
  if not (d/f'{tool}-time.log').exists(): continue
  rec[tool]=metrics(d/f'{tool}-time.log')
  p=d/f'{tool}.log'; s=p.read_text(); rec[tool].update(log_sha256=sha(p),log_bytes=p.stat().st_size)
  if tool=='aeneas': rec[tool]['full_log']=s
 p=d/'compiler.llbc'
 if p.exists(): rec['llbc']={'sha256':sha(p),'bytes':p.stat().st_size,'has_errors':json.loads(p.read_text()).get('has_errors')}
 if (d/'tool-sha256.txt').exists(): rec['tool_pins']=(d/'tool-sha256.txt').read_text()
 out[name]=rec
out['gates']={}
for p in sorted((R/'gates').glob('*/receipt.json')):
 out['gates'][p.parent.name]=json.loads(p.read_text())
 if p.parent.name in ['after-glue','after-migration','after-pr1']:
  out['gates'][p.parent.name]['stdout']=(p.parent/'stdout.log').read_text()
for f in ['before-masked/fixtures/masked-fixture-gate.json','after-masked/fixtures/masked-fixture-gate.json','before-ordered/counter.json','after-ordered/counter.json','pr1.json']:
 p=R/'gates'/f
 if p.exists(): out['gates'][f]=json.loads(p.read_text())
p=R/'gates/PASS'; out['gates']['all_pass']=p.exists()
p=R/'gates/reservation-waits.jsonl'
if p.exists(): out['reservation_waits']=[json.loads(s) for s in p.read_text().splitlines()]
for name in ['kani-records_equal_copied_reference','kani-records_equal_parametric_roots','failed-parametric-stubbing']:
 d=R/name
 if (d/'time.log').exists():
  out[name]=dict(metrics(d/'time.log'),full_log=(d/'kani.log').read_text())
  src=d/'records-full.rs' if (d/'records-full.rs').exists() else R/'source/tools/r1-builder-reference/records.rs'
  out[name]['proof_source_sha256']=sha(src)
  if (d/'cgroup-monitor.json').exists(): out[name]['cgroup_monitor']=json.loads((d/'cgroup-monitor.json').read_text())
  if (d/'stop-review.json').exists():
   out[name]['stop_review']=json.loads((d/'stop-review.json').read_text())
   out[name]['status']='stopped without verdict'
   out[name]['true_peak_rss_kib']=None
  if name=='kani-records_equal_copied_reference':
   out[name].update(status='stopped without verdict',last_sampled_cbmc_rss_kib=3649508,stop_reason='Whole record cone, including concrete empty-root hashes; dominant substep not profiled. No unchanged solver retry or cap increase.',true_peak_rss_kib=None)
print(json.dumps(out))
'''.replace('RR',repr(R))
r=subprocess.run(['ssh',HOST,'python3 -'],input=script,text=True,capture_output=True,check=True)
out=json.loads(r.stdout)
out.update(host_directory=R,source_revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),source_dirty=bool(subprocess.check_output(['git','status','--porcelain'],text=True).strip()),scope=dict(MemoryHigh='6G',MemoryMax='8G',MemorySwapMax=0,TasksMax=64),axioms='N/A: Rust/extraction receipts. Lean audit receipts are in attempts.jsonl.')
root=HERE.parents[3]
if (HERE/'builder-d83-evidence/validator-gates.json').exists():
    out['gates']={'all_pass':out['gates']['all_pass'],'evidence':'validator-gates.json'}
out['current_source_sha256']={p:hashlib.sha256((root/p).read_bytes()).hexdigest() for p in ['crates/aspis-statement/src/pool_v1/pair_forest_trace.rs','crates/aspis-statement/src/pool_v1/pair_forest_copy_builder.rs','tools/r1-builder-reference/records.rs']}
(HERE/'builder-d83-evidence/continuation.json').write_text(json.dumps(out,indent=2)+'\n')
print('extractions',len([x for x in out if x.startswith(('attempt','evidence-'))]),'gate receipts',len(out['gates']),'all_pass',out['gates']['all_pass'])
