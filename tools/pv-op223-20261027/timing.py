"""Research first, then candidate, five identical-coin calls per fixture."""
from pathlib import Path
import subprocess,json,hashlib,statistics,time,sys
H=Path('/home/dombarker/project-offloads/codex-pv-op223-20261027');O=H/(sys.argv[1] if len(sys.argv)>1 else 'quiet-timing');O.mkdir(exist_ok=False)
rows={};snapshots=[]
def snapshot(label):
 cgroot=Path('/sys/fs/cgroup/user.slice/user-1000.slice/user@1000.service/app.slice');scopes=[]
 for p in cgroot.glob('*.scope'):
  try:
   procs=(p/'cgroup.procs').read_text().split()
   if procs:scopes.append(dict(scope=p.name,memory_current=(p/'memory.current').read_text().strip(),memory_max=(p/'memory.max').read_text().strip(),processes=subprocess.run(['ps','-p',','.join(procs),'-o','pid=,comm=,args='],capture_output=True,text=True).stdout))
  except FileNotFoundError:pass
 r=dict(label=label,utc=time.time(),uptime=subprocess.check_output(['uptime'],text=True).strip(),loadavg=Path('/proc/loadavg').read_text().strip(),scopes=scopes)
 snapshots.append(r);(O/'host-load.json').write_text(json.dumps(snapshots,indent=2)+'\n');return r
snapshot('before research')
for who in ['baseline','candidate']:
 binary=H/who/'bin/prover_rw_gate'
 pin=json.loads((H/who/'build-fixture/binary-pins.json').read_text())['prover_rw_gate']
 assert hashlib.sha256(binary.read_bytes()).hexdigest()==pin['sha256'] and binary.stat().st_size==pin['bytes'],(who,'fixture binary changed')
 if who=='candidate':snapshot('before candidate')
 for sample in range(5):
  subprocess.run(['python3',str(H/'quiet-preflight.py'),str(O/f'quiet-{who}-before-{sample}.json')],check=True,stdout=subprocess.DEVNULL)
  subprocess.run([str(binary),str(O/who/f'sample-{sample}'),str(100+sample),'1'],check=True)
  subprocess.run(['python3',str(H/'quiet-preflight.py'),str(O/f'quiet-{who}-after-{sample}.json')],check=True,stdout=subprocess.DEVNULL)
 rows[who]=dict(revision=(H/who/'source-revision.txt').read_text().strip(),binary_sha256=hashlib.sha256(binary.read_bytes()).hexdigest(),binary_bytes=binary.stat().st_size,command_template=[str(binary),str(O/who/'sample-N'),'100+N','1'],samples=5)
 snapshot('after '+who)
timing=[];comparisons=[]
for fixture in ['transfer','withdrawal']:
 values={}
 for who in rows:
  values[who]=[json.loads((O/who/f'sample-{coin-100}'/f'{fixture}-{coin}'/'result.json').read_text())['seconds'] for coin in range(100,105)]
 med={k:statistics.median(v) for k,v in values.items()}
 timing.append(dict(fixture=fixture,n=5,seconds=values,median_seconds=med,ratio=med['candidate']/med['baseline'],under_15_seconds=med['candidate']<15,within_10_percent=med['candidate']<=1.1*med['baseline']))
 for coin in range(100,105):
  files={}
  for name in ['public.bin','proof.bin']:
   a=(O/'baseline'/f'sample-{coin-100}'/f'{fixture}-{coin}'/name).read_bytes();b=(O/'candidate'/f'sample-{coin-100}'/f'{fixture}-{coin}'/name).read_bytes()
   files[name]=dict(byte_identical=a==b,research_sha256=hashlib.sha256(a).hexdigest(),candidate_sha256=hashlib.sha256(b).hexdigest(),research_bytes=len(a),candidate_bytes=len(b))
  comparisons.append(dict(fixture=fixture,coin=coin,files=files))
r=dict(research_first=True,same_host_session=True,rows=rows,timing=timing,comparisons=comparisons,passed=all(t['under_15_seconds'] and t['within_10_percent'] for t in timing) and all(f['byte_identical'] for c in comparisons for f in c['files'].values()),scope='Fixture medians only; no universal cost or side-channel theorem')
(O/'comparison.json').write_text(json.dumps(r,indent=2)+'\n');print(json.dumps({k:v for k,v in r.items() if k!='comparisons'},indent=2));sys.exit(0 if r['passed'] else 3)
