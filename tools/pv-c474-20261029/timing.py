"""Actual baseline/draft clients, alternating paired fixture calls in own quiet window."""
from pathlib import Path
import hashlib,json,os,statistics,subprocess,time
H=Path('/home/dombarker/project-offloads/codex-pv-c474-20261029');O=H/'timing';O.mkdir(exist_ok=False)
M=H.parent/'QUIET_WINDOW.json';owner='pv-c474-20261029'
B={'baseline':H/'native-target/release/devnet_spend','draft':H/'native-target/client/devnet_spend'}
rows=[]
def write(p,x):p.write_text(json.dumps(x,indent=2)+'\n')
def guard(label):
 m=json.loads(M.read_text());assert m['owner']==owner and time.time()+40<m['until'],m
 subprocess.run(['python3',str(H/'quiet-preflight.py'),str(O/(label+'-quiet.json'))],check=True,stdout=subprocess.DEVNULL)
def thermal():
 d={}
 for p in Path('/sys/devices/system/cpu').glob('cpu[0-9]*/thermal_throttle/*'):
  if p.name.endswith(('_count','_total_time_ms')):d[str(p)]=int(p.read_text())
 assert d,'thermal counters unavailable'
 return d
pins={k:dict(path=str(p),sha256=hashlib.sha256(p.read_bytes()).hexdigest(),bytes=p.stat().st_size) for k,p in B.items()};write(O/'binary-pins.json',pins)
# Requests were produced by the existing actual-client/SBF fixture gate.
requests={f:json.loads((H/'runtime-private-final/default'/f/'request.json').read_text()) for f in ['transfer','withdrawal']}
def public_key(label):
 raw=hashlib.sha256(label.encode()).digest();n=int.from_bytes(raw,'big');out=''
 alphabet='123456789ABCDEFGHJKLMNPQRSTUVWXYZabcdefghijkmnopqrstuvwxyz'
 while n:n,r=divmod(n,58);out=alphabet[r]+out
 return '1'*(len(raw)-len(raw.lstrip(b'\0')))+out
start=time.time()
for i in range(10):
 order=['baseline','draft'] if i%2==0 else ['draft','baseline']
 guard(f'{i}-before');before=thermal();pair=[]
 for f,q0 in requests.items():
  for side in order:
   guard(f'{i}-{f}-{side}-before')
   q=dict(q0);q['proof_dir']=str(O/f'{i}-{f}-{side}-proof')
   # Fresh fixture-only public nonce labels per pair, same in both experiments.
   # No private key/account exists for these labels; all ledgers are retained.
   q['proof_accounts']=[public_key(f'PV-C474 pair {i} {f} attempt {j}') for j in range(8)]
   t=time.monotonic();r=subprocess.run(['taskset','--cpu-list','0-21',str(B[side])],input=json.dumps(q),capture_output=True,text=True,timeout=90)
   wall=time.monotonic()-t
   assert r.returncode==0 and not r.stderr,(r.returncode,r.stderr)
   v=json.loads(r.stdout);assert v['attempts']==1,(f,side,v['attempts'])
   pair.append(dict(pair=i,fixture=f,side=side,order=order,seconds=v['prove_wall_seconds'],process_wall_seconds=wall,attempts=v['attempts']))
   guard(f'{i}-{f}-{side}-after')
 after=thermal();deltas={k:after[k]-v for k,v in before.items()};assert all(x>=0 for x in deltas.values())
 throttled=any(x>0 for x in deltas.values())
 for r in pair:r.update(throttled=throttled,thermal_counter_deltas=deltas)
 rows.extend(pair);write(O/'progress.json',rows);print('TIMING_PAIR',i,'throttled',throttled,flush=True)
summary=[]
for f in requests:
 groups={}
 for name,rs in [('all',rows),('unthrottled',[r for r in rows if not r['throttled']])]:
  values={k:[r['seconds'] for r in rs if r['fixture']==f and r['side']==k] for k in B}
  med={k:statistics.median(v) if v else None for k,v in values.items()}
  ratio=med['draft']/med['baseline'] if med['baseline'] else None
  groups[name]=dict(values=values,median_seconds=med,ratio=ratio,delta_percent=100*(ratio-1) if ratio else None,within_10_percent=ratio<=1.10 if ratio else None)
 n=len(groups['unthrottled']['values']['draft'])
 summary.append(dict(fixture=f,groups=groups,minimum_unthrottled_pairs=5,verdict=('PASS' if groups['unthrottled']['within_10_percent'] else 'FAIL') if n>=5 else 'UNDECIDED: insufficient unthrottled pairs'))
write(O/'summary.json',dict(start=start,end=time.time(),pairs=10,rows=rows,summary=summary,scope='Finite actual client fixture timing; stdout field and external process duration. Throttled ratios are descriptive, not an unthrottled performance pass. Timing remains observable under D478.'))
print(json.dumps(summary,indent=2),flush=True)
