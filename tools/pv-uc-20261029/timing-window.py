"""Prepared only: D561 paired timing in a lead-arranged pv-uc-timing window."""
from pathlib import Path
import hashlib,json,os,statistics,subprocess,time,importlib.util,signal
H=Path('/home/dombarker/project-offloads/codex-pv-uc-20261029');CONTROL=H.parent/'codex-pv-c474-20261029';O=H/'final-gates/timing-d561';O.mkdir(exist_ok=False)
spec=importlib.util.spec_from_file_location('guard',Path(__file__).with_name('timing-window-guard.py'));g=importlib.util.module_from_spec(spec);spec.loader.exec_module(g)
monitor=g.Monitor()
B={'baseline':CONTROL/'artifacts/baseline-devnet_spend','draft':H/'native-target/client/user_client'}
rows=[]
def write(p,x):p.write_text(json.dumps(x,indent=2)+'\n')
def guard(label):
 write(O/(label+'-quiet.json'),monitor.poll())
def invoke(command,**kwargs):
 # Keep monitoring while communicate waits for the actual prover.
 import threading
 p=subprocess.Popen(command,**kwargs,start_new_session=True)
 result={}
 def communicate():
  try:result['out'],result['err']=p.communicate(result_input,timeout=90)
  except BaseException as e:result['error']=e
 t=threading.Thread(target=communicate,daemon=True);t.start()
 try:
  while t.is_alive():
   monitor.poll();t.join(0.02)
  monitor.poll()
  if 'error' in result:raise result['error']
  return subprocess.CompletedProcess(command,p.returncode,result['out'],result['err'])
 except BaseException:
  if p.poll() is None:
   os.killpg(p.pid,signal.SIGTERM)
   try:p.wait(timeout=5)
   except subprocess.TimeoutExpired:os.killpg(p.pid,signal.SIGKILL);p.wait()
  t.join(timeout=5)
  raise
def thermal():
 d={}
 for p in Path('/sys/devices/system/cpu').glob('cpu[0-9]*/thermal_throttle/*'):
  if p.name.endswith(('_count','_total_time_ms')):d[str(p)]=int(p.read_text())
 assert d,'thermal counters unavailable'
 return d
assert hashlib.sha256(B['baseline'].read_bytes()).hexdigest()=='30d883a8d97f12c315898aaf9170eb7a542b5e935881f089506fd4601ddb6a20'
expected=json.loads((H/'final-gates/d561-final/build.json').read_text())['binaries']['user_client']['sha256']
assert hashlib.sha256(B['draft'].read_bytes()).hexdigest()==expected
pins={k:dict(path=str(p),sha256=hashlib.sha256(p.read_bytes()).hexdigest(),bytes=p.stat().st_size) for k,p in B.items()};write(O/'binary-pins.json',pins)
# Requests were produced by the existing actual-client/SBF fixture gate.
requests={f:json.loads((CONTROL/'runtime-private-final/default'/f/'request.json').read_text()) for f in ['transfer','withdrawal']}
def public_key(label):
 raw=hashlib.sha256(label.encode()).digest();n=int.from_bytes(raw,'big');out=''
 alphabet='123456789ABCDEFGHJKLMNPQRSTUVWXYZabcdefghijkmnopqrstuvwxyz'
 while n:n,r=divmod(n,58);out=alphabet[r]+out
 return '1'*(len(raw)-len(raw.lstrip(b'\0')))+out
fixtures=json.loads((H/'fixture-inputs.json').read_text())
start=time.time();pair=[];i=None
try:
 with monitor:
  preflight=monitor.poll();write(O/'preflight.json',preflight)
  assert preflight['load'][0]<2.0, 'pre-admission/load requirement'
  for i in range(10):
   order=['baseline','draft'] if i%2==0 else ['draft','baseline']
   guard(f'{i}-before');before=thermal();pair=[]
   for f,q0 in requests.items():
    for side in order:
     guard(f'{i}-{f}-{side}-before')
     q=dict(q0);q['proof_dir']=str(O/f'{i}-{f}-{side}-proof')
     # Fresh fixture-only public nonce labels per pair, same in both experiments.
     # No private key/account exists for these labels; all ledgers are retained.
     q['proof_accounts']=[public_key(f'PV-UC D561 pair {i} {f} attempt {j}') for j in range(8)]
     rfd=None
     if side=='draft':
      q.pop('note');q.update(lane_leaf_sets=fixtures['lane_leaf_sets'],withdrawal_amount=250)
      rfd,wfd=os.pipe();os.write(wfd,bytes.fromhex(fixtures['records'][0 if f=='transfer' else 1]));os.close(wfd);q['wallet_bytes_fd']=rfd
     result_input=json.dumps(q)
     t=time.monotonic()
     try:r=invoke(['taskset','--cpu-list','0-21',str(B[side])],stdin=subprocess.PIPE,stdout=subprocess.PIPE,stderr=subprocess.PIPE,text=True,pass_fds=() if rfd is None else (rfd,))
     finally:
      if rfd is not None:os.close(rfd)
     wall=time.monotonic()-t
     assert r.returncode==0 and not r.stderr,(r.returncode,r.stderr)
     v=json.loads(r.stdout);assert v['attempts']==1,(f,side,v['attempts'])
     pair.append(dict(pair=i,fixture=f,side=side,order=order,seconds=v['prove_wall_seconds'],process_wall_seconds=wall,attempts=v['attempts']))
     # Keep actual completed calls even when the following quiet check rejects
     # the pair. This never admits a sample rejected by that check.
     write(O/'calls-before-postcheck.json',dict(accepted_rows=rows,current_pair=pair))
     guard(f'{i}-{f}-{side}-after')
   after=thermal();deltas={k:after[k]-v for k,v in before.items()};assert all(x>=0 for x in deltas.values())
   throttled=any(x>0 for x in deltas.values())
   for r in pair:r.update(throttled=throttled,thermal_counter_deltas=deltas)
   rows.extend(pair);write(O/'progress.json',rows)
   for f in requests:
    rolling={k:statistics.median([r['seconds'] for r in rows if r['fixture']==f and r['side']==k]) for k in B}
    assert rolling['draft']/rolling['baseline']<=1.10,dict(stop_gate='+10%',fixture=f,rolling_medians=rolling)
   print('TIMING_PAIR',i,'throttled',throttled,flush=True)
  summary=[]
  for f in requests:
   groups={}
   for name,rs in [('all',rows),('unthrottled',[r for r in rows if not r['throttled']])]:
    values={k:[r['seconds'] for r in rs if r['fixture']==f and r['side']==k] for k in B}
    med={k:statistics.median(v) if v else None for k,v in values.items()}
    ratio=med['draft']/med['baseline'] if med['baseline'] else None
    process_values={k:[r['process_wall_seconds'] for r in rs if r['fixture']==f and r['side']==k] for k in B}
    process_med={k:statistics.median(v) if v else None for k,v in process_values.items()}
    groups[name]=dict(process_wall_median_seconds=process_med,values=values,median_seconds=med,ratio=ratio,delta_percent=100*(ratio-1) if ratio else None,within_10_percent=ratio<=1.10 if ratio else None)
   n=len(groups['all']['values']['draft'])
   summary.append(dict(fixture=f,groups=groups,minimum_paired_samples=10,under_15_seconds=groups['all']['median_seconds']['draft']<15,verdict=('PASS' if groups['all']['within_10_percent'] and groups['all']['median_seconds']['draft']<15 else 'FAIL') if n==10 else 'INCOMPLETE'))
  guard('final-before-summary')
  write(O/'summary.json',dict(start=start,end=time.time(),pairs=10,rows=rows,summary=summary,scope='Finite actual client fixture timing; stdout field and external process duration. D359(A) owner-adopted gate evidence: measured under throttling, paired; ratio <=1.10 and candidate median <15 seconds. No universal unthrottled upper bound claimed. Timing remains observable under D478.'))
  print(json.dumps(summary,indent=2),flush=True)
except BaseException as exc:
 write(O/'INVALID.json',dict(valid=False,pair=i,error=repr(exc),guard_failure=monitor.failure,unaccepted_current_pair=pair,previous_complete_rows=rows,checks=monitor.checks))
 raise
finally:monitor.close()
