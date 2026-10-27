"""Five alternating optimized whole-prover pairs; indicative, outside quiet window."""
from pathlib import Path
import hashlib,json,statistics,subprocess,time
H=Path('/home/dombarker/project-offloads/codex-pv-batch2-20261027'); O=H/'timing-precheck';O.mkdir(exist_ok=False)
quiet=H.parent/'QUIET_WINDOW.json'
def clear():
 assert not quiet.exists() or time.time()>=json.loads(quiet.read_text())['until'],'quiet window active'
rows=[]
for sample in range(5):
 for who in (['baseline','candidate'] if sample%2==0 else ['candidate','baseline']):
  clear();binary=H/who/'bin/prover_rw_gate';out=O/who/f'sample-{sample}'
  start=time.monotonic();r=subprocess.run([str(binary),str(out),str(100+sample),'1'],stdout=open(O/f'{who}-{sample}.log','w'),stderr=subprocess.STDOUT)
  rows.append(dict(sample=sample,who=who,binary_sha256=hashlib.sha256(binary.read_bytes()).hexdigest(),exit_status=r.returncode,wall_seconds=time.monotonic()-start))
  (O/'runs.json').write_text(json.dumps(rows,indent=2)+'\n');assert r.returncode==0,rows[-1]
results=[]
for fixture in ['transfer','withdrawal']:
 values={who:[json.loads((O/who/f'sample-{i}'/f'{fixture}-{100+i}'/'result.json').read_text())['seconds'] for i in range(5)] for who in ['baseline','candidate']}
 med={k:statistics.median(v) for k,v in values.items()};ratio=med['candidate']/med['baseline']
 results.append(dict(fixture=fixture,seconds=values,medians=med,ratio=ratio,within_three_percent=ratio<=1.03))
r=dict(scope='Indication only; outside quiet window; not adoption gate',baseline_revision='73070ddd512bc4e79edfc0db714fb64dc74e87b8',candidate_revision='5b92d4aa185486cc735c0a3eb75a3024171ca482',alternating_pairs=5,results=results,passed=all(x['within_three_percent'] for x in results))
(O/'comparison.json').write_text(json.dumps(r,indent=2)+'\n');print(json.dumps(r,indent=2));raise SystemExit(0 if r['passed'] else 3)
