"""Ordered current-producer byte gate, reusing only frozen baseline outputs."""
from pathlib import Path
import subprocess,hashlib,json,time,re,os
H=Path('/home/dombarker/project-offloads/codex-pv-batch2-20261027');W=H/'candidate';D=H/'batch2f-fixture-gate-001';D.mkdir(exist_ok=False)
start_epoch=time.time();closure=W/'batch2f-lean-40847/receipt/receipt.json';cr=json.loads(closure.read_text());assert cr['exit_status']==0 and closure.stat().st_mtime<start_epoch
pins=json.loads((H/'batch2f-binary-pins.json').read_text());binary=Path(pins['binaries']['prover_rw_gate']['path']);sha=hashlib.sha256(binary.read_bytes()).hexdigest();assert sha==pins['binaries']['prover_rw_gate']['sha256']
base_runs=json.loads((H/'timing-precheck/runs.json').read_text());base=[r for r in base_runs if r['who']=='baseline'];assert len(base)==5 and all(r['source_revision']=='73070ddd512bc4e79edfc0db714fb64dc74e87b8' and r['exit_status']==0 for r in base)
plan=dict(source_revision=pins['source_revision'],binary_sha256=sha,baseline_revision='73070ddd512bc4e79edfc0db714fb64dc74e87b8',baseline_binary_sha256=sorted({r['binary_sha256'] for r in base}),closure_receipt=str(closure),closure_completed_before_start=True,started_epoch=start_epoch,expected_time='Optimized full prover, including named P_R1 certificate generation/elimination; no compilation; five two-fixture processes',keys='No key deletion or transactions; retain fixture ledgers')
(D/'plan.json').write_text(json.dumps(plan,indent=2)+'\n');runs=[];rows=[]
for i in range(5):
 out=D/'candidate'/f'sample-{i}';out.parent.mkdir(exist_ok=True)
 cmd=['timeout','180',str(binary),str(out),str(100+i),'1'];tf=D/f'sample-{i}.time.log'
 print('current fixture pair',i,'coin',100+i,'optimized P_R1 generation/elimination',flush=True)
 t=time.monotonic()
 with (D/f'sample-{i}.log').open('w') as f:r=subprocess.run(['/usr/bin/time','-v','-o',str(tf),*cmd],cwd=W/'src',stdout=f,stderr=subprocess.STDOUT)
 tl=tf.read_text();m=lambda pat:int(re.search(pat,tl)[1]);run=dict(sample=i,command=cmd,source_revision=pins['source_revision'],exit_status=r.returncode,wall_seconds=time.monotonic()-t,peak_rss_kib=m(r'Maximum resident set size \(kbytes\):\s*(\d+)'),swaps=m(r'Swaps:\s*(\d+)'),load_average=os.getloadavg(),print_axioms='N/A native fixture execution')
 runs.append(run);(D/'runs.json').write_text(json.dumps(runs,indent=2)+'\n');assert r.returncode==0,run
 for fixture in ['transfer','withdrawal']:
  paths=dict(baseline=H/'timing-precheck/baseline'/f'sample-{i}'/f'{fixture}-{100+i}',candidate=out/f'{fixture}-{100+i}');files={}
  for name in ['proof.bin','public.bin']:
   bs={k:(p/name).read_bytes() for k,p in paths.items()};files[name]=dict(identical=bs['baseline']==bs['candidate'],hashes={k:hashlib.sha256(b).hexdigest() for k,b in bs.items()},bytes={k:len(b) for k,b in bs.items()})
  results={k:json.loads((p/'result.json').read_text()) for k,p in paths.items()};fields=['status','attempts','callbacks','proof_sha256','audit'];same={k:results['baseline'].get(k)==results['candidate'].get(k) for k in fields}
  row=dict(fixture=fixture,coin=100+i,files=files,result_fields=same);rows.append(row)
  passed=all(f['identical'] for f in files.values()) and all(same.values())
  report=dict(passed=passed and len(rows)==10,completed_pairs=len(rows),comparisons=rows,plan=plan)
  (D/'comparison.json').write_text(json.dumps(report,indent=2)+'\n')
  if not passed:raise SystemExit('STOP fixture disagreement: '+fixture+' '+str(100+i))
print('ordered fixture-byte gate PASS; ten transfer/withdrawal outputs match73070ddd51',flush=True)
